/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Amitsur.Descent
public import ReasLib.Algebra.Amitsur.Homotopy
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Cosimplicial.ChangeOfRings
public import ReasLib.Algebra.Module.DescentDatum.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

/- Remark 35.3.11 (1): cartesian modules over a cosimplicial algebra are the module
presheaves whose scalar-extension comparison is invertible for every simplex map. -/
@[stacks 039Y] #check
  (@CosimplicialAlgebra.CartesianModule :
    ∀ {R : Type u} [CommRing R],
      CosimplicialObject (CommAlgCat.{u} R) → Type (u + 1))

/- Remark 35.3.11 (2), source clause (1): faithfully flat base change reduces
effectiveness of module descent data to effectiveness after scalar extension. -/
@[stacks 039Y] #check
  (@Module.DescentDatum.allEffective_of_baseChange :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R']
      [Module.FaithfullyFlat R A] [Module.FaithfullyFlat R R'],
      (∀ (N' : Type u) [AddCommGroup N'] [Module R' N']
        [Module (R' ⊗[R] A) N'] [IsScalarTower R' (R' ⊗[R] A) N']
        [SMulCommClass R' (R' ⊗[R] A) N']
        (D' : Module.DescentDatum R' (R' ⊗[R] A) N'), D'.IsEffective) →
      ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
        [IsScalarTower R A N] [SMulCommClass R A N]
        (D : Module.DescentDatum R A N), D.IsEffective)

/- Remark 35.3.11 (3), source clause (2): module descent data are equivalent to
cartesian modules over the Amitsur cosimplicial algebra. -/
@[stacks 039Y] #check
  (@Algebra.Amitsur.Descent.equivalence :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A],
      ModuleCat.DescentData (Algebra.ofId R A).toRingHom ≌
        CosimplicialAlgebra.CartesianModule
          (Algebra.Amitsur.cosimplicialAlgebra R A))

/- Remark 35.3.11 (4), source clause (3): a section of `R → A` contracts the
Amitsur cosimplicial algebra onto the constant cosimplicial algebra at `R`. -/
@[stacks 039Y] #check
  (@Algebra.Amitsur.homotopyEquivOfSection :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A],
      (A →ₐ[R] R) →
        CosimplicialObject.HomotopyEquiv
          ((CosimplicialObject.const (CommAlgCat.{u} R)).obj (CommAlgCat.of R R))
          (Algebra.Amitsur.cosimplicialAlgebra R A))

/- Remark 35.3.11 (5), source clause (4): scalar extension along a cosimplicial
homotopy equivalence induces an equivalence between cartesian-module categories. -/
@[stacks 039Y] #check
  (@CosimplicialAlgebra.CartesianModule.extension_isEquivalence :
    ∀ {R : Type u} [CommRing R]
      {A B : CosimplicialObject (CommAlgCat.{u} R)}
      (e : CosimplicialObject.HomotopyEquiv A B),
      (CosimplicialAlgebra.CartesianModule.extension e).IsEquivalence)
