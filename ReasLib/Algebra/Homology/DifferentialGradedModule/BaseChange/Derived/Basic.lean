/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.CategoryTheory.Functor.Derived.Transformation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Left-Derived Base Change of Differential Graded Modules

Ordinary ground-ring base change is derived on the canonical DG derived categories and
compared with relative derived tensor extension.  This foundational leaf has no K-flatness,
right-derived, restriction, or degree-zero dependencies.  The DGA carrier universes for `A` and
`S` are independent; the ordinary base-change module and derived-category carrier is
`max uA uS`.
-/

@[expose] public section

noncomputable section

universe uR uS uA

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.BaseChange

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- Ordinary base change on the homotopy category, followed by the canonical localization of
base-changed DG modules. -/
@[stacks 0BYZ "homotopy source for ordinary derived base change"]
abbrev sourceFunctor (A : CochainDGAlgebra.{uR, uA} R) :
    CategoryTheory.Functor (K R (DifferentialGradedModule.{uR, max uA uS} A))
      (DifferentialGradedModule.Derived.Category.{uR, max uA uS} (algebra (S := S) A)) :=
  (dgFunctor (S := S) A).mapK ⋙
    DifferentialGradedModule.Derived.Q (algebra (S := S) A)

/-- Pointwise existence of the total left derived functor of ordinary base change. -/
@[stacks 0BYZ "existence predicate for ordinary derived base change"]
abbrev HasDerivedFunctor (A : CochainDGAlgebra.{uR, uA} R) : Prop :=
  Functor.LeftDerived.EverywhereDefined (sourceFunctor (S := S) A)
    (DifferentialGradedModule.quasiIso A)

/-- Property P resolutions define ordinary ground-ring base change at every derived object. -/
instance hasDerivedFunctor (A : CochainDGAlgebra.{uR, uA} R) :
    HasDerivedFunctor (S := S) A := sorry

/-- The total left derived functor of ordinary ground-ring base change. -/
@[stacks 0BYZ "derived ground-ring base change for differential graded modules"]
noncomputable def derivedFunctor (A : CochainDGAlgebra.{uR, uA} R) :
    CategoryTheory.Functor (DifferentialGradedModule.Derived.Category.{uR, max uA uS} A)
      (DifferentialGradedModule.Derived.Category.{uR, max uA uS} (algebra (S := S) A)) :=
  (sourceFunctor (S := S) A).totalLeftDerived
    (DifferentialGradedModule.Derived.Q A) (DifferentialGradedModule.quasiIso A)

/-- The canonical comparison from derived base change to ordinary base change on the homotopy
category. -/
@[stacks 0BYZ "derived-to-underived base-change counit"]
noncomputable def derivedCounit (A : CochainDGAlgebra.{uR, uA} R) :
    DifferentialGradedModule.Derived.Q A ⋙ derivedFunctor (S := S) A ⟶
      sourceFunctor (S := S) A :=
  (sourceFunctor (S := S) A).totalLeftDerivedCounit
    (DifferentialGradedModule.Derived.Q A) (DifferentialGradedModule.quasiIso A)

/-- The canonical base-change functor with its counit satisfies the universal property of a
total left derived functor. -/
instance derivedFunctor_isLeftDerived (A : CochainDGAlgebra.{uR, uA} R) :
    (derivedFunctor (S := S) A).IsLeftDerivedFunctor (derivedCounit (S := S) A)
      (DifferentialGradedModule.quasiIso A) := sorry

/-- At the homotopy-level source, ordinary ground-ring base change agrees with relative tensor
extension along `A ⟶ A ⊗[R] S`. -/
@[stacks 0BYZ "homotopy comparison with relative tensor extension"]
noncomputable def sourceIso (A : CochainDGAlgebra.{uR, uA} R) :
    sourceFunctor (S := S) A ≅
      DifferentialGradedBimodule.Tensor.derivedSourceFunctor (extension (S := S) A) :=
  Functor.isoWhiskerRight (comparisonK (S := S) A)
    (DifferentialGradedModule.Derived.Q (algebra (S := S) A))

/-- Derived ground-ring base change is canonically isomorphic to relative derived tensor
extension along `A ⟶ A ⊗[R] S`.  This comparison of left-derived models does not require a
K-flatness assumption on `A`. -/
@[stacks 0BYZ "derived base change is relative derived tensor extension"]
noncomputable def derivedIso (A : CochainDGAlgebra.{uR, uA} R) :
    derivedFunctor (S := S) A ≅
      DifferentialGradedBimodule.Tensor.derivedFunctor (extension (S := S) A) :=
  Functor.leftDerivedNatIso
    (derivedFunctor (S := S) A)
    (DifferentialGradedBimodule.Tensor.derivedFunctor (extension (S := S) A))
    (derivedCounit (S := S) A)
    (DifferentialGradedBimodule.Tensor.derivedCounit (extension (S := S) A))
    (DifferentialGradedModule.quasiIso A) (sourceIso (S := S) A)

/-- The derived base-change isomorphism is characterized by compatibility with the two
canonical derived-to-underived comparisons. -/
theorem derivedIso_fac (A : CochainDGAlgebra.{uR, uA} R) :
    Functor.whiskerLeft (DifferentialGradedModule.Derived.Q A)
        (derivedIso (S := S) A).hom ≫
      DifferentialGradedBimodule.Tensor.derivedCounit (extension (S := S) A) =
    derivedCounit (S := S) A ≫ (sourceIso (S := S) A).hom := sorry

/-- The comparison from relative derived tensor product to the localized ordinary base-change
model of a specific DG module. -/
@[stacks 0BYZ "objectwise derived base-change comparison"]
noncomputable def representationComparison (A : CochainDGAlgebra.{uR, uA} R)
    (M : DifferentialGradedModule.{uR, max uA uS} A) :
    (DifferentialGradedBimodule.Tensor.derivedFunctor (extension (S := S) A)).obj
        ((DifferentialGradedModule.Derived.Q A).obj
          ((DifferentialGradedModule.toK A).obj M)) ⟶
      (sourceFunctor (S := S) A).obj ((DifferentialGradedModule.toK A).obj M) :=
  (derivedIso (S := S) A).inv.app
      ((DifferentialGradedModule.Derived.Q A).obj
        ((DifferentialGradedModule.toK A).obj M)) ≫
    (derivedCounit (S := S) A).app ((DifferentialGradedModule.toK A).obj M)

end DifferentialGradedModule.BaseChange
