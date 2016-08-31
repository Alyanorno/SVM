--{-# LANGUAGE GeneralizedNewtypeDeriving, BangPatterns, FlexibleContexts, TypeOperators, PartialTypeSignatures  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, BangPatterns, FlexibleContexts, TypeOperators, ScopedTypeVariables #-}


import Data.List
import Data.List.Split
import Data.String
import Data.Function
import Data.Maybe

import Control.Monad
import Control.Exception (assert)

import Text.Read

import Test.QuickCheck

import Data.Array.Repa (Array, U, D, Z(..), (:.)(..), (+^), (-^), (*^), (/^), computeP, computeS, Any(..), All(..))
import Data.Array.Repa.Repr.Unboxed (Unbox(..))
import Data.Array.Repa.Eval (Elt(..))
import qualified Data.Array.Repa as R
import qualified Data.HashMap.Strict as Map

import System.IO hiding (EQ, LT, GT)


type Bibliography = Map.HashMap String Int

test_insertIfNew :: [String] -> Bool
test_insertIfNew a = (length (nub a)) == (Map.size $ (foldr insertIfNew (Map.empty) a :: Bibliography))

insertIfNew :: String -> Bibliography -> Bibliography
insertIfNew a b = if Map.member a b then b else Map.insert a (Map.size b) b

getKnownKey :: String -> Bibliography -> Int
getKnownKey a b = maybe (error "Unknown key") (\a -> a) $ Map.lookup a b

getKey :: String -> Bibliography -> Maybe Int
getKey a b = Map.lookup a b


main :: IO ()
main = do
	lines <- liftM (map words . splitOn "\n") $ readFile "values.txt"
	(p :: [[String]], v :: [[String]]) <- return . (\(a,b) -> (a, map (drop 1) b)) . unzip . map (break (== ":")) $ lines

	bibliography :: Bibliography <- return . foldr insertIfNew (Map.singleton "" 0) . concat $ p

	let biggest = foldr (\x xs -> max (length x) xs) 0 p
	p' :: [String] <- return . concat . map (\a -> let l = length a in if l == biggest then a else a ++ (replicate (biggest-l) "")) $ p
	p'' :: [Float] <- return . map fromIntegral . map ((flip getKnownKey) bibliography) $ p'

	v' :: [Float] <- return . map read . concat $ v

	putStrLn $ id "Input from file"
	print [p, v]

	print [p'', v']
	putStrLn $ id  "-----------"
	putStrLn $ id  ""

	let size = length p --5 :: Int
--	print $ R.fromListUnboxed (Z :. size :. biggest) p''
--	print $ createKernelMatrix (dot) 0.2 $ R.fromListUnboxed (Z :. size :. biggest) p''
	solution <- let
		points = R.fromListUnboxed (Z :. size :. biggest) p''
		values = R.fromListUnboxed (Z :. size) v'
		epsilon = 0.2
		iterations = 1000
		in return $ solve (dot) points values epsilon iterations
		-- Easy to replace with more complicated kernelfunctions like this
--		mlp :: Data a => a -> FloatArray -> FloatArray -> Float
--		in return $ solve (mlp <data>) points values epsilon iterations
	(\(kernelFunction, a, b, points) -> do
		putStrLn $ id  "Solution found"
		print a
		print b
		print $ createKernelMatrix kernelFunction 0.2 points
		putStrLn $ id  "---------------"
		putStrLn $ id  ""
		) solution

	fix (\loop -> do
		t :: String <- getLine
		t' :: [Float] <- return . map fromIntegral . mapMaybe (flip getKey bibliography) . words $ t
		t'' :: [Float] <- let l = length t'; max = biggest in return $ case compare l max of
			EQ -> t'
			LT -> t' ++ replicate (max-l) (0 :: Float)
			GT -> take max t'
		print t''
		points <- return $ R.fromListUnboxed (Z :. (1 :: Int) :. biggest) t''
		print $ simulate points solution
		putStrLn "----------------"
		putStrLn $ id  ""
		loop)


toArray :: Unbox e => [e] -> Array U (Z :. Int) e
toArray a = R.fromListUnboxed (Z :. (length a)) a

type FloatMatrix = Array U (Z :. Int :. Int) Float
type FloatArray = Array U (Z :. Int) Float
type IntArray = Array U (Z :. Int) Int
type KernelFunction = FloatArray -> FloatArray -> Float
type Solution = (KernelFunction, FloatArray, Float, FloatMatrix)


simulate :: FloatMatrix -> Solution -> FloatArray
simulate points (kernelFunction, a, b, solvedPoints) = computeS $ R.map ((+b) . f . row points) indexs
	where
	indexs = toArray [0..n-1]
	(Z :. n :. _) = R.extent points

	sindexs = toArray [0..sn-1]
	(Z :. sn :. _) = R.extent solvedPoints

	f :: FloatArray -> Float
	f x = a `dot` (computeS $ R.map (kernelFunction x . row solvedPoints) sindexs)

solve :: (FloatArray -> FloatArray -> Float) -> FloatMatrix -> FloatArray -> Float -> Int -> Solution
solve kernelFunction points values epsilon iterations = (kernelFunction, a, b, points)
	where
	a = computeS $ R.zipWith (\x y -> x - b * y) v nu
	b :: Float = (sum v) `safeDiv` (sum nu)
		where sum = R.sumAllS

	nu = conjugateGradientMethod zeroes ones kernel epsilon iterations
	v = conjugateGradientMethod zeroes values kernel epsilon iterations

	zeroes = toArray (replicate n (0 :: Float))
	ones = toArray (replicate n (1 :: Float))
	(Z :. n) = R.extent values

	kernel = createKernelMatrix kernelFunction 0.2 points


createKernelMatrix :: (FloatArray -> FloatArray -> Float) -> Float -> FloatMatrix -> FloatMatrix
createKernelMatrix kernelFunction cost points = R.fromListUnboxed (Z :. n :. n) $ [eval a b | a <- range, b <- range]
	where
	range = [0..n-1]
	(Z :. n :. _) = R.extent points
	eval i l 
		| i <= l = kernelFunction (points `row` i) (points `row` l) + if i == l then cost else 0
		| otherwise = 0

conjugateGradientMethod :: FloatArray -> FloatArray -> FloatMatrix -> Float -> Int -> FloatArray
conjugateGradientMethod x r k epsilon iterations = loop x r r norm iterations
	where 
	norm :: Float = r `dot` r
	loop :: FloatArray -> FloatArray -> FloatArray -> Float -> Int -> FloatArray
	loop x p r delta iterations
		| iterations == 0 = x
		| delta' < epsilon * norm || delta' /= delta' = x -- When stuck delta becomes really small until its NaN, NaN /= NaN = True
		| otherwise = loop x' p' r' delta' (iterations-1)
		where
		delta' = (r' `dot` r')

		ap = k `matrixArrayMult` p
		a = delta `safeDiv` (p `dot` ap)
		b = delta' `safeDiv` delta

		x' :: FloatArray = computeS $ (checkNaN ("x is NaN when: " ++ show ap ++ show delta') x) +^ (R.map (*a) p)
		p' :: FloatArray = computeS $ (checkNaN ("r' is NaN when: " ++ show ap ++ show delta') r') *^ (R.map (*b) p)
		r' :: FloatArray = computeS $ (checkNaN ("r is NaN when: " ++ show ap ++ show delta') r) -^ (R.map (*a) ap)

checkNaN s x = x --if x == x then x else error s

safeDiv :: (Eq a, Floating a) => a -> a -> a
(safeDiv) x 0 = x / 0.0001
(safeDiv) x y = x / y

test_matrixArrayMult :: Bool
test_matrixArrayMult = (R.fromListUnboxed (Z :. size :. size) [1..4]) `matrixArrayMult` (toArray [5,6]) == toArray [17, 39]
	where size = 2 :: Int

matrixArrayMult :: FloatMatrix -> FloatArray -> FloatArray
(matrixArrayMult) m v = computeS $ R.map ((v `dot`).(m `row`)) indexs
	where indexs = let (Z :. n) = R.extent v in R.fromListUnboxed (Z :. (n :: Int)) [0..n-1]

column :: FloatMatrix -> Int -> FloatArray
(column) matrix index = computeS $ R.slice matrix (Any :. index)

row :: FloatMatrix -> Int -> FloatArray
(row) matrix index = computeS $ R.slice matrix (Any :. index :. All)


withSameLength vec f = forAll (vectorOf size arbitrary) $ \b -> f $ toArray b
	where (Z :. size) = R.extent vec

prop_commutativeDot :: FloatArray -> Property
prop_commutativeDot a = withSameLength a $ \b -> a `dot` b == b `dot` a

prop_distributiveDot :: IntArray -> Property
prop_distributiveDot a = withSameLength a $ \b -> withSameLength b $ \c -> a `dot` (b `add` c) == (a `dot` b) + (a `dot` c)
	where (add) x y = computeS $ x +^ y

prop_bilinearDot :: IntArray -> Property
prop_bilinearDot a = withSameLength a $ \b -> withSameLength b $ \c ->
	(a `add` c) `dot` b == a `dot` b + c `dot` b &&
	a `dot` (b `add` c) == a `dot` b + a `dot` c
	where add x y = computeS $ x +^ y

prop_scalaMultiplicationDot :: IntArray -> Int -> Int -> Property
prop_scalaMultiplicationDot a c1 c2 = withSameLength a $ \b -> (a `m` c1) `dot` (b `m` c2) == (a `dot` b) * c1 * c2
	where (m) vec s = computeS $ R.map (*s) vec

test_dot :: Bool
test_dot = a `dot` b == 32
	where
	a = toArray ([1,2,3] :: [Float])
	b = toArray ([4,5,6] :: [Float])

dot :: (Elt a, Unbox a, Num a) => Array U (Z :. Int) a -> Array U (Z :. Int) a -> a
(dot) x y = R.sumAllS $ x *^ y

