--type Stack = [Int]

-- pop :: {elems (s) != {}} 
--
-- State Stack Int 
--
-- {\exits x. v = x /\ elems (s') = elems (s) -- {(x)} /\ len (s') = len (s) -1}
--
-- pop :: State Stack Int 
--
-- -- push :: i : Int -> {true} 
--
-- State Stack () 
--
-- {elems (s') = elems (s) U {(i)} /\ len (s') = len (s) + 1 }
--
-- push :: Int -> State Stack () 
--
-- -- goal :: Int -> {elems (s) = {}} 
--
-- State Stack Int 
--
-- {elems (s') C= elems (s) U {(i)} /\ len (s') = len (s) - 1}
--
-- goal :: Int -> State Stack Int 
--
-- goal i = 
--
-- 	 pop >>= \x . ... —incorrect—
--
-- 	 push i >>= \_. pop >>= return i —incorrect—
--
-- 	 push i >>= \_ . pop >>= \_. pop — correct—
--
-- 	 push i >>= \_. pop >>= \_. pop >>= \_. pop —incorrect—
--
