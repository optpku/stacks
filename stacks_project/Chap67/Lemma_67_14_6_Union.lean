/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Lemma_67_14_5_Inclusion

/-!
# Structure-sheaf Mayer–Vietoris data for closed subspaces

The structure sheaves of two closed subspaces of an algebraic space, viewed as
`𝒪_X`-modules, fit into a Mayer–Vietoris short complex whose terms are the
quotients of `𝒪_X` by the corresponding quasi-coherent ideal sheaves.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The structure sheaf of the closed subspace cut out by a quasi-coherent ideal
sheaf `I`, viewed as an `𝒪_X`-module by the quotient `𝒪_X ⟶ 𝒪_X / I`. -/
noncomputable abbrev closedSubspaceStructureSheafOn (I : IdealSubobject X)
    [IsQuasiCoherent I] : X.Modules :=
  cokernel I.arrow

/-- The pushforward `i_* 𝒪_Z` of the structure sheaf of the closed subspace cut
out by `I` along `subschemeι I`. -/
noncomputable abbrev closedSubspacePushforwardStructureSheaf (I : IdealSubobject X)
    [IsQuasiCoherent I] : X.Modules :=
  (Modules.pushforward (subschemeι I)).obj
    (SheafOfModules.unit (structureSheaf (subscheme I)))

/-- The quotient presentation of the closed-subspace structure sheaf is isomorphic
to the pushforward `i_* 𝒪_Z` along `subschemeι I`. -/
theorem closedSubspaceStructureSheafOn_eq (I : IdealSubobject X) [IsQuasiCoherent I] :
    Nonempty
      (closedSubspaceStructureSheafOn I ≅
        closedSubspacePushforwardStructureSheaf I) :=
  sorry

/-- The comparison of closed-subspace structure sheaves induced by an inclusion of
closed subspaces, as the cokernel map of `Subobject.ofLE`. -/
noncomputable def closedSubspaceStructureSheafMap {I J : IdealSubobject X}
    [IsQuasiCoherent I] [IsQuasiCoherent J] (h : I ≤ J) :
    closedSubspaceStructureSheafOn I ⟶ closedSubspaceStructureSheafOn J :=
  cokernel.map I.arrow J.arrow (Subobject.ofLE I J h) (𝟙 _)
    ((Category.comp_id I.arrow).trans (Subobject.ofLE_arrow h).symm)

/-- The comparison map of closed-subspace structure sheaves is the cokernel map
induced by `Subobject.ofLE`. -/
theorem closedSubspaceStructureSheafMap_eq {I J : IdealSubobject X}
    [IsQuasiCoherent I] [IsQuasiCoherent J] (h : I ≤ J) :
    closedSubspaceStructureSheafMap h =
      cokernel.map I.arrow J.arrow (Subobject.ofLE I J h) (𝟙 _)
        ((Category.comp_id I.arrow).trans (Subobject.ofLE_arrow h).symm) :=
  rfl

/-- The first map in the structure-sheaf Mayer–Vietoris sequence for two closed
subspaces. -/
noncomputable abbrev schemeTheoreticUnionToProduct (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    closedSubspaceStructureSheafOn (I ⊓ J) ⟶
      Limits.prod (closedSubspaceStructureSheafOn I) (closedSubspaceStructureSheafOn J) :=
  Limits.prod.lift
    (closedSubspaceStructureSheafMap (inf_le_left : I ⊓ J ≤ I))
    (closedSubspaceStructureSheafMap (inf_le_right : I ⊓ J ≤ J))

/-- The first component of `schemeTheoreticUnionToProduct` is the canonical map
to the structure sheaf of the first closed subspace. -/
theorem schemeTheoreticUnionToProduct_fst (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnionToProduct I J ≫ Limits.prod.fst =
      closedSubspaceStructureSheafMap (inf_le_left : I ⊓ J ≤ I) :=
  Limits.prod.lift_fst _ _

/-- The second component of `schemeTheoreticUnionToProduct` is the canonical map
to the structure sheaf of the second closed subspace. -/
theorem schemeTheoreticUnionToProduct_snd (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnionToProduct I J ≫ Limits.prod.snd =
      closedSubspaceStructureSheafMap (inf_le_right : I ⊓ J ≤ J) :=
  Limits.prod.lift_snd _ _

/-- The second map in the structure-sheaf Mayer–Vietoris sequence for two closed
subspaces, sending a pair of sections to their difference on the intersection. -/
noncomputable abbrev schemeTheoreticProductToIntersection (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    Limits.prod (closedSubspaceStructureSheafOn I) (closedSubspaceStructureSheafOn J) ⟶
      closedSubspaceStructureSheafOn (I ⊔ J) :=
  Limits.prod.fst ≫ closedSubspaceStructureSheafMap (le_sup_left : I ≤ I ⊔ J) -
    Limits.prod.snd ≫ closedSubspaceStructureSheafMap (le_sup_right : J ≤ I ⊔ J)

/-- The two maps in the structure-sheaf Mayer–Vietoris sequence compose to zero. -/
theorem schemeTheoreticUnionToProduct_comp_schemeTheoreticProductToIntersection
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnionToProduct I J ≫ schemeTheoreticProductToIntersection I J = 0 :=
  sorry

/-- The Mayer–Vietoris sequence of structure sheaves associated to two closed
subspaces, as a short complex of `𝒪_X`-modules. -/
noncomputable def schemeTheoreticUnionShortComplex (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] : ShortComplex X.Modules :=
  ShortComplex.mk (schemeTheoreticUnionToProduct I J)
    (schemeTheoreticProductToIntersection I J)
    (schemeTheoreticUnionToProduct_comp_schemeTheoreticProductToIntersection I J)

/-- The first morphism of `schemeTheoreticUnionShortComplex` is
`schemeTheoreticUnionToProduct`. -/
theorem schemeTheoreticUnionShortComplex_f (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    (schemeTheoreticUnionShortComplex I J).f = schemeTheoreticUnionToProduct I J :=
  rfl

/-- The second morphism of `schemeTheoreticUnionShortComplex` is
`schemeTheoreticProductToIntersection`. -/
theorem schemeTheoreticUnionShortComplex_g (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    (schemeTheoreticUnionShortComplex I J).g = schemeTheoreticProductToIntersection I J :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
