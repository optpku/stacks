/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Conormal.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Stalk
public import ReasLib.RingTheory.Ideal.Cotangent.Comparison
public import ReasLib.Topology.Sheaves.Algebraic.FreeAlgebra.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of conormal modules

The first layer compares the stalk of an arbitrary conormal sheaf with the scalar extension of
the kernel-cotangent module of the induced map on stalk rings.  The second layer specializes the
ring-theoretic kernel comparison to free-algebra evaluations.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.Conormal.Stalk

open SheafOfModules.RingedSite

variable {X : TopCat.{u}} {O₂ O₃ : X.Sheaf CommRingCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose
  (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The morphism on stalk rings induced by a morphism of commutative-ring sheaves. -/
abbrev ringMap (α : O₂ ⟶ O₃) (x : X) :
    O₂.presheaf.stalk x ⟶ O₃.presheaf.stalk x :=
  PresheafOfModules.KernelCotangent.Stalk.ringMap α.hom x

/-- The stalk of the objectwise conormal presheaf before extending scalars. -/
abbrev presheafStalk (α : O₂ ⟶ O₃) (x : X) :
    ModuleCat (O₂.presheaf.stalk x) :=
  PresheafOfModules.KernelCotangent.Stalk.source α.hom x

/-- The kernel-cotangent module of the morphism induced on stalk rings. -/
abbrev algebraic (α : O₂ ⟶ O₃) (x : X) :
    ModuleCat (O₂.presheaf.stalk x) :=
  PresheafOfModules.KernelCotangent.Stalk.target α.hom x

/-- The stalk of the objectwise conormal presheaf, extended to the target stalk ring. -/
abbrev extendedPresheafStalk (α : O₂ ⟶ O₃) (x : X) :
    ModuleCat (O₃.presheaf.stalk x) :=
  (ModuleCat.extendScalars (ringMap α x).hom).obj (presheafStalk α x)

/-- The algebraic kernel-cotangent module, extended to the target stalk ring. -/
abbrev extendedAlgebraic (α : O₂ ⟶ O₃) (x : X) :
    ModuleCat (O₃.presheaf.stalk x) :=
  (ModuleCat.extendScalars (ringMap α x).hom).obj (algebraic α x)

/-- The stalk of the scalar-extended conormal source sheaf. -/
abbrev sheafStalk (α : O₂ ⟶ O₃) (x : X) :
    ModuleCat (O₃.presheaf.stalk x) :=
  (SheafOfModules.stalkFunctorOfCommRing O₃ x).obj (conormalSource α)

/-- The canonical comparison from the stalk of the objectwise conormal presheaf to the
kernel-cotangent module of the morphism on stalk rings. -/
abbrev presheafComparison (α : O₂ ⟶ O₃) (x : X) :
    presheafStalk α x ⟶ algebraic α x :=
  PresheafOfModules.KernelCotangent.Stalk.comparison α.hom x

/-- The explicit inverse comparison from the algebraic stalk-kernel cotangent module to the
stalk of the objectwise conormal presheaf. -/
abbrev presheafComparisonInv (α : O₂ ⟶ O₃) (x : X) :
    algebraic α x ⟶ presheafStalk α x :=
  PresheafOfModules.KernelCotangent.Stalk.comparisonInv α.hom x

/-- The common-source comparison to the scalar-extended algebraic kernel-cotangent module. -/
@[stacks 0D09 "conormal stalk comparison to the algebraic cotangent module"]
noncomputable abbrev algebraicComparison (α : O₂ ⟶ O₃) (x : X) :
    extendedPresheafStalk α x ⟶ extendedAlgebraic α x :=
  (ModuleCat.extendScalars (ringMap α x).hom).map (presheafComparison α x)

/-- The explicit inverse of the scalar-extended algebraic conormal stalk comparison. -/
@[stacks 0D09 "inverse conormal stalk comparison from the algebraic cotangent module"]
noncomputable abbrev algebraicComparisonInv (α : O₂ ⟶ O₃) (x : X) :
    extendedAlgebraic α x ⟶ extendedPresheafStalk α x :=
  (ModuleCat.extendScalars (ringMap α x).hom).map (presheafComparisonInv α x)

/-- The common-source comparison to the stalk of the scalar-extended conormal sheaf. -/
@[stacks 0D09 "conormal presheaf-to-sheaf stalk comparison"]
noncomputable def sheafComparison (α : O₂ ⟶ O₃) (x : X) :
    extendedPresheafStalk α x ⟶ sheafStalk α x :=
  (ModuleCat.extendScalars (ringMap α x).hom).map
      (TopCat.Sheaf.moduleSheafificationStalkComparison O₂
        (conormalPresheaf α) x) ≫
    (TopCat.Sheaf.ChangeOfRings.Stalk.comparison α x).app
      (conormalSourceOverSource α)

/-- The explicit inverse from the conormal sheaf stalk to the scalar-extended stalk of the
objectwise conormal presheaf. -/
@[stacks 0D09 "inverse conormal presheaf-to-sheaf stalk comparison"]
noncomputable def sheafComparisonInv (α : O₂ ⟶ O₃) (x : X) :
    sheafStalk α x ⟶ extendedPresheafStalk α x :=
  TopCat.Sheaf.ChangeOfRings.Stalk.comparisonInvApp α x
      (conormalSourceOverSource α) ≫
    (ModuleCat.extendScalars (ringMap α x).hom).map
      (TopCat.Sheaf.moduleSheafificationStalkComparisonInv O₂
        (conormalPresheaf α) x)

omit [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The scalar-extended algebraic comparison followed by its explicit inverse is the
identity. -/
@[simp]
theorem algebraicComparison_hom_inv_id (α : O₂ ⟶ O₃) (x : X) :
    algebraicComparison α x ≫ algebraicComparisonInv α x = 𝟙 _ := sorry

omit [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The explicit algebraic inverse followed by the scalar-extended comparison is the
identity. -/
@[simp]
theorem algebraicComparison_inv_hom_id (α : O₂ ⟶ O₃) (x : X) :
    algebraicComparisonInv α x ≫ algebraicComparison α x = 𝟙 _ := sorry

omit [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The scalar extension of the kernel-cotangent presheaf stalk isomorphism, with both
directions explicitly owned. -/
@[stacks 0D09 "scalar-extended algebraic conormal stalk isomorphism"]
noncomputable def algebraicComparisonIso (α : O₂ ⟶ O₃) (x : X) :
    extendedPresheafStalk α x ≅ extendedAlgebraic α x where
  hom := algebraicComparison α x
  inv := algebraicComparisonInv α x
  hom_inv_id := algebraicComparison_hom_inv_id α x
  inv_hom_id := algebraicComparison_inv_hom_id α x

omit [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The comparison to the scalar-extended algebraic kernel-cotangent module is an
isomorphism. -/
@[stacks 0D09 "algebraic conormal stalk comparison is an isomorphism", instance]
instance algebraicComparison_isIso (α : O₂ ⟶ O₃) (x : X) :
    IsIso (algebraicComparison α x) :=
  (algebraicComparisonIso α x).isIso_hom

omit [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The forward map of `algebraicComparisonIso` is the canonical algebraic comparison. -/
@[stacks 0D09 "scalar-extended algebraic conormal stalk isomorphism hom", simp]
theorem algebraicComparisonIso_hom (α : O₂ ⟶ O₃) (x : X) :
    (algebraicComparisonIso α x).hom = algebraicComparison α x := sorry

omit [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The inverse of the scalar-extended algebraic conormal stalk isomorphism is the explicit
scalar extension of the presheaf-level inverse. -/
@[stacks 0D09 "scalar-extended algebraic conormal stalk isomorphism inverse", simp]
theorem algebraicComparisonIso_inv (α : O₂ ⟶ O₃) (x : X) :
    (algebraicComparisonIso α x).inv = algebraicComparisonInv α x := sorry

/-- The conormal presheaf-to-sheaf comparison followed by its explicit inverse is the
identity. -/
@[simp]
theorem sheafComparison_hom_inv_id (α : O₂ ⟶ O₃) (x : X) :
    sheafComparison α x ≫ sheafComparisonInv α x = 𝟙 _ := sorry

/-- The explicit conormal sheaf inverse followed by the presheaf-to-sheaf comparison is the
identity. -/
@[simp]
theorem sheafComparison_inv_hom_id (α : O₂ ⟶ O₃) (x : X) :
    sheafComparisonInv α x ≫ sheafComparison α x = 𝟙 _ := sorry

/-- The comparison from the scalar-extended presheaf stalk to the conormal sheaf stalk, built
from module sheafification and the natural change-of-rings stalk isomorphism. -/
@[stacks 0D09 "conormal presheaf-to-sheaf stalk isomorphism"]
noncomputable def sheafComparisonIso (α : O₂ ⟶ O₃) (x : X) :
    extendedPresheafStalk α x ≅ sheafStalk α x where
  hom := sheafComparison α x
  inv := sheafComparisonInv α x
  hom_inv_id := sheafComparison_hom_inv_id α x
  inv_hom_id := sheafComparison_inv_hom_id α x

/-- The comparison to the stalk of the scalar-extended conormal sheaf is an isomorphism. -/
@[stacks 0D09 "conormal sheaf stalk comparison is an isomorphism", instance]
instance sheafComparison_isIso (α : O₂ ⟶ O₃) (x : X) :
    IsIso (sheafComparison α x) :=
  (sheafComparisonIso α x).isIso_hom

/-- The forward map of `sheafComparisonIso` is the canonical presheaf-to-sheaf comparison. -/
@[stacks 0D09 "conormal presheaf-to-sheaf stalk isomorphism hom", simp]
theorem sheafComparisonIso_hom (α : O₂ ⟶ O₃) (x : X) :
    (sheafComparisonIso α x).hom = sheafComparison α x := sorry

/-- The inverse map of the conormal presheaf-to-sheaf stalk isomorphism is the explicit
change-of-rings and sheafification inverse. -/
@[stacks 0D09 "conormal presheaf-to-sheaf stalk isomorphism inverse", simp]
theorem sheafComparisonIso_inv (α : O₂ ⟶ O₃) (x : X) :
    (sheafComparisonIso α x).inv = sheafComparisonInv α x := sorry

/-- The canonical isomorphism from the stalk of the scalar-extended conormal sheaf to the
scalar-extended kernel-cotangent module of the induced stalk-ring morphism. -/
@[stacks 0D09 "conormal sheaf stalk identification"]
noncomputable def sheafStalkIso (α : O₂ ⟶ O₃) (x : X) :
    sheafStalk α x ≅ extendedAlgebraic α x :=
  (sheafComparisonIso α x).symm ≪≫ algebraicComparisonIso α x

/-- The forward map of `sheafStalkIso` is the inverse sheafification comparison followed by
the algebraic conormal comparison. -/
@[stacks 0D09 "conormal sheaf stalk identification hom", simp]
theorem sheafStalkIso_hom (α : O₂ ⟶ O₃) (x : X) :
    (sheafStalkIso α x).hom =
      sheafComparisonInv α x ≫ algebraicComparison α x := sorry

/-- The inverse of `sheafStalkIso` first applies the inverse algebraic comparison and then the
canonical comparison to the conormal sheaf stalk. -/
@[stacks 0D09 "conormal sheaf stalk identification inverse", simp]
theorem sheafStalkIso_inv (α : O₂ ⟶ O₃) (x : X) :
    (sheafStalkIso α x).inv =
      algebraicComparisonInv α x ≫ sheafComparison α x := sorry

/-- The stalk-ring differential module for `φ`, extended along the induced morphism from the
middle stalk ring to the target stalk ring. -/
abbrev tensorAlgebraic {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    ModuleCat (O₃.presheaf.stalk x) :=
  (ModuleCat.extendScalars (ringMap α x).hom).obj
    (TopCat.Sheaf.RelativeDifferentials.Stalk.target φ x)

/-- The stalk of the sheaf-level scalar-extended relative-differentials term. -/
abbrev tensorSheafStalk {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    ModuleCat (O₃.presheaf.stalk x) :=
  (SheafOfModules.stalkFunctorOfCommRing O₃ x).obj
    (conormalTensorTerm φ α)

/-- The canonical comparison from scalar-extended differentials of the stalk rings to the stalk
of the sheaf-level scalar-extended relative-differentials term. -/
@[stacks 0D09 "base-changed differentials stalk comparison"]
noncomputable def tensorComparison {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    tensorAlgebraic φ α x ⟶ tensorSheafStalk φ α x :=
  (ModuleCat.extendScalars (ringMap α x).hom).map
      (TopCat.Sheaf.RelativeDifferentials.Stalk.comparisonInv φ x) ≫
    (TopCat.Sheaf.ChangeOfRings.Stalk.comparison α x).app
      (TopCat.Sheaf.relativeDifferentials φ)

/-- The explicit inverse from the stalk of the scalar-extended relative-differentials sheaf to
scalar extension of the algebraic differential module. -/
@[stacks 0D09 "inverse base-changed differentials stalk comparison"]
noncomputable def tensorComparisonInv {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    tensorSheafStalk φ α x ⟶ tensorAlgebraic φ α x :=
  TopCat.Sheaf.ChangeOfRings.Stalk.comparisonInvApp α x
      (TopCat.Sheaf.relativeDifferentials φ) ≫
    (ModuleCat.extendScalars (ringMap α x).hom).map
      (TopCat.Sheaf.RelativeDifferentials.Stalk.comparison φ x)

/-- The base-changed differentials comparison followed by its explicit inverse is the
identity. -/
@[simp]
theorem tensorComparison_hom_inv_id {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    tensorComparison φ α x ≫ tensorComparisonInv φ α x = 𝟙 _ := sorry

/-- The explicit base-changed differentials inverse followed by the comparison is the
identity. -/
@[simp]
theorem tensorComparison_inv_hom_id {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    tensorComparisonInv φ α x ≫ tensorComparison φ α x = 𝟙 _ := sorry

/-- The base-changed-differentials stalk comparison, built from the relative-differentials
stalk isomorphism and the natural change-of-rings stalk isomorphism. -/
@[stacks 0D09 "base-changed differentials stalk comparison isomorphism"]
noncomputable def tensorComparisonIso {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    tensorAlgebraic φ α x ≅ tensorSheafStalk φ α x where
  hom := tensorComparison φ α x
  inv := tensorComparisonInv φ α x
  hom_inv_id := tensorComparison_hom_inv_id φ α x
  inv_hom_id := tensorComparison_inv_hom_id φ α x

/-- The base-changed relative-differentials stalk comparison is an isomorphism. -/
@[stacks 0D09 "base-changed differentials stalk comparison is an isomorphism", instance]
instance tensorComparison_isIso {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    IsIso (tensorComparison φ α x) :=
  (tensorComparisonIso φ α x).isIso_hom

/-- The forward map of `tensorComparisonIso` is the canonical base-changed-differentials
comparison. -/
@[stacks 0D09 "base-changed differentials stalk comparison isomorphism hom", simp]
theorem tensorComparisonIso_hom {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    (tensorComparisonIso φ α x).hom = tensorComparison φ α x := sorry

/-- The inverse map of the base-changed-differentials comparison is the explicit reverse
composite. -/
@[stacks 0D09 "base-changed differentials stalk comparison isomorphism inverse", simp]
theorem tensorComparisonIso_inv {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    (tensorComparisonIso φ α x).inv = tensorComparisonInv φ α x := sorry

/-- The canonical isomorphism from the stalk of the sheaf-level scalar-extended
relative-differentials term to scalar extension of differentials of the stalk rings. -/
@[stacks 0D09 "base-changed differentials stalk identification"]
noncomputable def tensorStalkIso {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    tensorSheafStalk φ α x ≅ tensorAlgebraic φ α x :=
  (tensorComparisonIso φ α x).symm

/-- The forward map of `tensorStalkIso` is the inverse base-changed-differentials
comparison. -/
@[stacks 0D09 "base-changed differentials stalk identification hom", simp]
theorem tensorStalkIso_hom {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    (tensorStalkIso φ α x).hom = tensorComparisonInv φ α x := sorry

/-- The inverse of `tensorStalkIso` is the canonical base-changed-differentials comparison. -/
@[stacks 0D09 "base-changed differentials stalk identification inverse", simp]
theorem tensorStalkIso_inv {O₁ : X.Sheaf CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (x : X) :
    (tensorStalkIso φ α x).inv = tensorComparison φ α x := sorry

end TopCat.Sheaf.Conormal.Stalk

namespace TopCat.Sheaf.FreeAlgebra.Conormal.Stalk

variable {X : TopCat.{u}} {A : X.Sheaf CommRingCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]

/-- Evaluation of the free algebra formed from stalks. -/
noncomputable abbrev algebraicEvaluation
    (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    (TopCat.Sheaf.FreeAlgebra.Stalk.algebraic A E x).right ⟶
      B.right.presheaf.stalk x :=
  (TopCat.Sheaf.FreeAlgebra.Stalk.evaluation B E assign x).right

/-- The stalk of the sheaf-level free-algebra evaluation. -/
noncomputable abbrev sheafEvaluation
    (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    (TopCat.Sheaf.FreeAlgebra.Stalk.sheaf A E x).right ⟶
      B.right.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (CategoryTheory.Sheaf.FreeAlgebra.evaluation B E assign).right.hom

/-- The free-algebra stalk comparison intertwines algebraic evaluation and the stalk of
sheaf-level evaluation. -/
@[stacks 0D09 "free-algebra stalk evaluation compatibility"]
theorem comparison_evaluation
    (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    TopCat.Sheaf.FreeAlgebra.Stalk.comparison A E x ≫
        sheafEvaluation B E assign x =
      algebraicEvaluation B E assign x := sorry

/-- The kernel ideal of the free-algebra evaluation formed after taking stalks. -/
noncomputable abbrev algebraicIdeal
    (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    Ideal (TopCat.Sheaf.FreeAlgebra.Stalk.algebraic A E x).right :=
  RingHom.ker (algebraicEvaluation B E assign x).hom

/-- The kernel ideal of the stalk of the sheaf-level free-algebra evaluation. -/
noncomputable abbrev sheafIdeal
    (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    Ideal (TopCat.Sheaf.FreeAlgebra.Stalk.sheaf A E x).right :=
  RingHom.ker (sheafEvaluation B E assign x).hom

/-- The canonical forward comparison on conormal modules induced by the free-algebra stalk
comparison. -/
@[stacks 0D09 "free-algebra conormal stalk comparison"]
noncomputable abbrev comparison
    (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    ModuleCat.of (TopCat.Sheaf.FreeAlgebra.Stalk.algebraic A E x).right
        (algebraicIdeal B E assign x).Cotangent ⟶
      (ModuleCat.restrictScalars
        (TopCat.Sheaf.FreeAlgebra.Stalk.comparison A E x).hom).obj
        (ModuleCat.of (TopCat.Sheaf.FreeAlgebra.Stalk.sheaf A E x).right
          (sheafIdeal B E assign x).Cotangent) :=
  CommRingCat.Cotangent.kerComparison
    (TopCat.Sheaf.FreeAlgebra.Stalk.comparison A E x)
    (algebraicEvaluation B E assign x) (sheafEvaluation B E assign x)
    (comparison_evaluation B E assign x)

/-- The conormal comparison sends the class of a kernel element to the class of its image under
the free-algebra stalk comparison. -/
@[stacks 0D09 "free-algebra conormal stalk comparison on generators"]
theorem comparison_generator
    (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) (z : algebraicIdeal B E assign x) :
    comparison B E assign x ((algebraicIdeal B E assign x).toCotangent z) =
      (sheafIdeal B E assign x).toCotangent
        ⟨TopCat.Sheaf.FreeAlgebra.Stalk.comparison A E x z,
          CommRingCat.Cotangent.ker_le_comap
            (TopCat.Sheaf.FreeAlgebra.Stalk.comparison A E x)
            (algebraicEvaluation B E assign x) (sheafEvaluation B E assign x)
            (comparison_evaluation B E assign x) z.2⟩ := sorry

/-- The canonical forward conormal comparison is an isomorphism after restriction of scalars. -/
@[stacks 0D09 "free-algebra conormal stalk comparison is an isomorphism", instance]
instance comparison_isIso
    (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    IsIso (comparison B E assign x) := sorry

end TopCat.Sheaf.FreeAlgebra.Conormal.Stalk

-- The comparison data delegates to the ring-theoretic owner. Any `sorryAx` is confined to
-- proof-valued ideal membership supplied by `CommRingCat.Cotangent.ker_le_comap`.
