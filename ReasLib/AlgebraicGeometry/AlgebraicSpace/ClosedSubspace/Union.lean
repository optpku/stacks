module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Inclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom

/-!
# Structure-sheaf Mayer–Vietoris data for closed subspaces

The structure sheaves of two closed subspaces of an algebraic space, viewed as
`𝒪_X`-modules by closed-immersion pushforward, fit into a short exact
Mayer–Vietoris sequence. Their scheme-theoretic union is the pushout over
their scheme-theoretic intersection.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The structure module of the closed subspace cut out by a quasi-coherent
ideal sheaf, pushed forward to the ambient algebraic space. -/
noncomputable abbrev closedSubspaceStructureSheafOn (I : IdealSubobject X)
    [IsQuasiCoherent I] : X.Modules :=
  Modules.pushforwardStructureModule (subschemeι I)

/-- The canonical restriction of pushed-forward structure modules associated
to an inclusion of closed subspaces. -/
noncomputable def closedSubspaceStructureSheafMap {I J : IdealSubobject X}
    [IsQuasiCoherent I] [IsQuasiCoherent J] (h : I ≤ J) :
    closedSubspaceStructureSheafOn I ⟶ closedSubspaceStructureSheafOn J :=
  (Modules.pushforward (subschemeι I)).map
      (Modules.unitToPushforwardObjUnit (inclusion h)) ≫
    (Modules.pushforwardComp (inclusion h) (subschemeι I)).hom.app
      (SheafOfModules.unit (structureSheaf (subscheme J))) ≫
    eqToHom (congrArg (fun f : subscheme J ⟶ X => Modules.pushforwardStructureModule f)
      (inclusion_subschemeι h))

/-- Restriction between pushed-forward structure modules is the pushforward
of the structure-module unit, followed by composition and the inclusion identity. -/
theorem closedSubspaceStructureSheafMap_eq {I J : IdealSubobject X}
    [IsQuasiCoherent I] [IsQuasiCoherent J] (h : I ≤ J) :
    closedSubspaceStructureSheafMap h =
      (Modules.pushforward (subschemeι I)).map
          (Modules.unitToPushforwardObjUnit (inclusion h)) ≫
        (Modules.pushforwardComp (inclusion h) (subschemeι I)).hom.app
          (SheafOfModules.unit (structureSheaf (subscheme J))) ≫
        eqToHom (congrArg (fun f : subscheme J ⟶ X => Modules.pushforwardStructureModule f)
          (inclusion_subschemeι h)) :=
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

/-- The pushed-forward structure modules of two closed subspaces, their
scheme-theoretic union, and their scheme-theoretic intersection form a short
exact Mayer–Vietoris sequence of modules on the ambient algebraic space. -/
theorem schemeTheoreticUnion_structureSheaf_shortExact (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    (schemeTheoreticUnionShortComplex I J).ShortExact :=
  sorry

/-- The scheme-theoretic union of two closed subspaces is their pushout over
the scheme-theoretic intersection in the category of algebraic spaces over the base. -/
theorem schemeTheoreticUnion_isPushout (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsPushout (inclusion (le_sup_left : I ≤ I ⊔ J))
      (inclusion (le_sup_right : J ≤ I ⊔ J))
      (inclusion (inf_le_left : I ⊓ J ≤ I))
      (inclusion (inf_le_right : I ⊓ J ≤ J)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
