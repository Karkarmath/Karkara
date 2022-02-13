import Test.HUnit
import System.Exit
import Check
import Data.Map as Map 
import Test.HUnit (Test)
 
-- Проверка термов с первого теоретического задания.

test1::Test
test1 = TestCase (do -- Ø ⊢ λx::A->A->G.λy::A.λz::B.xyy
                    let env = fromList []
                    let term = Lam "x" (TVar "A" :-> TVar "A" :-> TVar "G") $ Lam "y" (TVar "A") $ Lam "z" (TVar "B") $ Var "x" :@  Var "y"  :@ Var "y" 
                    let Just pp = eval env term
                    let ans = (TVar "A" :-> TVar "A" :-> TVar "G") :-> TVar "A" :-> TVar "B" :-> TVar "G"
                    assertEqual "" ans pp )

test2::Test
test2 = TestCase (do -- Ø ⊢ λx::(A->G)->A.λy::A->G.λz::B.y(xy)
                    let env = fromList []
                    let term = Lam "x" ((TVar "A" :-> TVar "G" ) :-> TVar "A") $ Lam "y" (TVar "A" :-> TVar "G") $ Lam "z" (TVar "B") $ Var "y" :@  ( Var "x"  :@ Var "y") 
                    let Just pp = eval env term
                    let ans = ((TVar "A" :-> TVar "G") :-> TVar "A") :-> (TVar "A" :-> TVar "G") :-> TVar "B" :-> TVar "G"
                    assertEqual "" ans pp )
 
test3::Test
test3 = TestCase (do -- Ø ⊢ λx::(A->B)->A.λy::A->A->B.x(λz::A.yz(x(yz))
                    let env = fromList []
                    let term = Lam "x" ((TVar "A" :-> TVar "B" ) :-> TVar "A") $ Lam "y" (TVar "A" :-> TVar "A" :-> TVar "B") $ Var "x" :@ (Lam "z" (TVar "A") $ Var "y" :@ Var "z" :@ (Var "x" :@ (Var "y" :@ Var "z")))
                    let Just pp = eval env term
                    let ans = ((TVar "A" :-> TVar "B") :-> TVar "A") :-> (TVar "A" :-> TVar "A" :-> TVar "B") :-> TVar "A"
                    assertEqual "" ans pp )
 
test4::Test
test4 = TestCase (do -- Ø ⊢ λx::(A->B)->A.λy::A->A->B.yTT, where T = x(λz::A.yz(x(yz)))
                    let env = fromList []
                    let subterm = Var "x" :@ (Lam "z" (TVar "A") $ Var "y" :@ Var  "z" :@ (Var "x" :@ (Var "y" :@ Var "z")))
                    let term = Lam "x" ((TVar "A" :-> TVar "B" ) :-> TVar "A") $ Lam "y" (TVar "A" :-> TVar "A" :-> TVar "B") $ Var "y" :@ subterm :@ subterm
                    let Just pp = eval env term
                    let ans = ((TVar "A" :-> TVar "B") :-> TVar "A") :-> (TVar "A" :-> TVar "A" :-> TVar "B") :-> TVar "B"
                    assertEqual "" ans pp )
 
test5::Test
test5 = TestCase (do -- x::A->B->G, y:A->B, z::A ⊢ xz(yz)
                    let env = fromList [  ( "x", TVar "A" :-> TVar "B" :-> TVar "G")
                                  ,  ( "y", TVar "A" :-> TVar "B")
                                  ,  ( "z", TVar "A") ]
                    let term = Var "x" :@ Var "z" :@ ( Var "y" :@ Var "z" )
                    let Just pp = eval env term
                    let ans = TVar "G" 
                    assertEqual "" ans pp )
 
test6::Test
test6 = TestCase (do -- y::G->A->B, z::G ⊢ λx::(A->B)->B.x(yz)
                    let env = fromList [  ( "y", TVar "G" :-> TVar "A" :-> TVar "B")
                                  ,  ( "z", TVar "G") ]
                    let term = Lam "x" ((TVar "A" :-> TVar "B") :-> TVar "B") $ Var "x" :@ (Var "y" :@ Var "z")
                    let Just pp = eval env term
                    let ans = ((TVar "A" :-> TVar "B") :-> TVar "B") :-> TVar "B" 
                    assertEqual "" ans pp )

test7::Test
test7 = TestCase (do -- x::A->A->B ⊢ λy::A.λz::B->G.z(xyy)
                    let env = fromList [  ( "x", TVar "A" :-> TVar "A" :-> TVar "B")
                                  ,  ( "z", TVar "G") ]
                    let term = Lam "y" (TVar "A") (Lam "z" (TVar "B" :-> TVar "G") (Var "z" :@ (Var "x" :@ Var "y" :@ Var "y")))
                    let Just pp = eval env term
                    let ans = TVar "A" :-> (TVar "B" :-> TVar "G") :-> TVar "G" 
                    assertEqual "" ans pp )

test8::Test
test8 = TestCase(do -- y::B->A->G.z::A ⊢ λx::A->B.y(xz)z 
                    let env = fromList [  ( "y", TVar "B" :-> TVar "A" :-> TVar "G")
                                ,  ( "z", TVar "A") ]
                    let term = Lam "x" (TVar "A" :-> TVar "B") (Var "y" :@ (Var "x" :@ Var "z") :@ Var "z")
                    let Just pp = eval env term
                    let ans = (TVar "A" :-> TVar "B") :-> TVar "G"
                    assertEqual "" ans pp )

-- Иные тесты

test9::Test
test9 = TestCase (do -- Ø ⊢ λx::A.x
                    let env = fromList []
                    let term = Lam "x" (TVar "A") (Var "x")
                    let Just pp = eval env term
                    let ans = TVar "A" :-> TVar "A" 
                    assertEqual "" ans pp )
 
test10::Test
test10 = TestCase (do -- Ø ⊢ λx::B.λy::A.x
                    let env = fromList []
                    let term = Lam "x" (TVar "B") $ Lam "y" (TVar "A") $ Var "x"
                    let Just pp = eval env term
                    let ans = TVar "B" :-> TVar "A" :-> TVar "B" 
                    assertEqual "" ans pp )
 
test11::Test
test11 = TestCase (do -- y::G->(A->B), z::G ⊢ λx::(A->B)->B.x(yz)
                    let env = fromList [  ( "y", TVar "G" :-> (TVar "A" :-> TVar "B"))
                                  ,  ( "z", TVar "G") ]
                    let term = Lam "x" ((TVar "A" :-> TVar "B") :-> TVar "B") $ Var "x" :@ (Var "y" :@ Var "z")
                    let Just pp = eval env term
                    let ans = ((TVar "A" :-> TVar "B") :-> TVar "B") :-> TVar "B"
                    assertEqual "" ans pp )
 
test12::Test
test12 = TestCase (do -- Ø ⊢ λx::A->B.λy::G->A.λz::G.x(yz)
                    let env = fromList [ ]
                    let term = Lam "x" (TVar "A" :-> TVar "B") $ Lam "y" (TVar "G" :-> TVar "A") $ Lam "z" (TVar "G") $ Var "x" :@ ( Var "y" :@ Var "z" )
                    let Just pp = eval env term
                    let ans = (TVar "A" :-> TVar "B") :-> ((TVar "G" :-> TVar "A") :-> (TVar "G" :-> TVar "B"))
                    assertEqual "" ans pp )
 
test13::Test
test13 = TestCase (do -- Ø ⊢ λy::G->A.λz::G.x(yz)
                    let env = fromList [ ]
                    let term = Lam "y" (TVar "G" :-> TVar "A") $ Lam "z" (TVar "G") $ Var "x" :@ ( Var "y" :@ Var "z" )
                    let pp = eval env term
                    assertEqual "" Nothing pp )
 
test14::Test
test14 = TestCase (do -- f::A->(B->X) ⊢ λg::C->A.λx::C.f(gx)
                    let env = fromList [("f",TVar "A" :-> (TVar "B" :-> TVar "X")) ]
                    let term = Lam "g" (TVar "C" :-> TVar "A") $ Lam "x" (TVar "C") $ Var "f" :@ ( Var "g" :@ Var "x" )
                    let Just pp = eval env term
                    let ans = (TVar "C" :-> TVar "A") :-> (TVar "C" :-> (TVar "B" :-> TVar "X"))
                    assertEqual "" ans pp )
 
test15::Test
test15 = TestCase (do -- f::X->(B->X) ⊢ λg::C->A.λx::C.f(gx)
                    let env = fromList [("f",TVar "X" :-> (TVar "B" :-> TVar "X")) ]
                    let term = Lam "g" (TVar "C" :-> TVar "A") $ Lam "x" (TVar "C") $ Var "f" :@ ( Var "g" :@ Var "x" )
                    let pp = eval env term
                    assertEqual "" Nothing pp )

main :: IO ()
main = do
    cs@(Counts _ _ errs fails) <- runTestTT $ TestList
        [ TestLabel "Ø ⊢ λx::A->A->G.λy::A.λz::B.xyy" test1
        , TestLabel "Ø ⊢ λx::(A->G)->A.λy::A->G.λz::B.y(xy)" test2
        , TestLabel "Ø ⊢ λx::(A->B)->A.λy::A->A->B.x(λz::A.yz(x(yz))" test3
        , TestLabel "Ø ⊢ λx::(A->B)->A.λy::A->A->B.yTT, where T = x(λz::A.yz(x(yz)))" test4
        , TestLabel "x::A->B->G, y:A->B, z::A ⊢ xz(yz)" test5
        , TestLabel "y::G->A->B, z::G ⊢ λx::(A->B)->B.x(yz)" test6
        , TestLabel "x::A->A->B ⊢ λy::A.λz::B->G.z(xyy)" test7
        , TestLabel "y::B->A->G.z::A ⊢ λx::A->B.y(xz)z " test8
        , TestLabel "Ø ⊢ λx::A.x" test9
        , TestLabel "Ø ⊢ λx::B.λy::A.x" test10
        , TestLabel "y::G->(A->B), z::G ⊢ λx::(A->B)->B.x(yz)" test11
        , TestLabel "Ø ⊢ λx::A->B.λy::G->A.λz::G.x(yz)" test12
        , TestLabel "Ø ⊢ λy::G->A.λz::G.x(yz)" test13
        , TestLabel "f::A->(B->X) ⊢ λg::C->A.λx::C.f(gx)" test14
        , TestLabel "f::X->(B->X) ⊢ λg::C->A.λx::C.f(gx)" test15]
    putStrLn (showCounts cs)
    if( errs > 0 || fails > 0 )
        then exitFailure
        else exitSuccess
