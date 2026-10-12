/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeCupProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/- Lemma 50.5.1 (1): the cup product on `H^*_{Hodge}(X/S)`, whose component
`H^i(X, Ω^a_{X/S}) ⊗ H^j(X, Ω^b_{X/S})` lands in
`H^(i+j)(X, Ω^(a+b)_{X/S})`, is associative. -/
@[stacks 0FM5] #check
  (AlgebraicGeometry.Scheme.DeRham.canonicalHodgeCupProduct_assoc :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [MonoidalCategory (coefficientDerived f)]
      [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
        coefficientDerived f).Monoidal]
      [(globalDerivedFunctor f).LaxMonoidal]
      (a b c : ℕ) (i j k : ℤ),
    (canonicalHodgeCupProduct f a b i j ▷ hodgeCohomologyObject f c k) ≫
        canonicalHodgeCupProduct f (a + b) c (i + j) k =
      (α_ (hodgeCohomologyObject f a i) (hodgeCohomologyObject f b j)
        (hodgeCohomologyObject f c k)).hom ≫
        (hodgeCohomologyObject f a i ◁ canonicalHodgeCupProduct f b c j k) ≫
        canonicalHodgeCupProduct f a (b + c) i (j + k) ≫
        eqToHom (congrArg₂ (hodgeCohomologyObject f)
          (Nat.add_assoc a b c).symm (add_assoc i j k).symm))

/- Lemma 50.5.1 (2): the cup product on `H^*_{Hodge}(X/S)` is graded
commutative for the total degree `a + i` on `H^i(X, Ω^a_{X/S})`. -/
@[stacks 0FM5] #check
  (AlgebraicGeometry.Scheme.DeRham.canonicalHodgeCupProduct_gradedComm :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [MonoidalCategory (coefficientDerived f)] [BraidedCategory (coefficientDerived f)]
      [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
        coefficientDerived f).Braided]
      [(globalDerivedFunctor f).LaxBraided]
      (a b : ℕ) (i j : ℤ),
    canonicalHodgeCupProduct f a b i j =
      (((a : ℤ) + i) * ((b : ℤ) + j)).negOnePow •
        ((β_ (hodgeCohomologyObject f a i)
          (hodgeCohomologyObject f b j)).hom ≫
          canonicalHodgeCupProduct f b a j i ≫
          eqToHom (congrArg₂ (hodgeCohomologyObject f)
            (Nat.add_comm b a) (add_comm j i))))

end AlgebraicGeometry.Scheme.DeRham
