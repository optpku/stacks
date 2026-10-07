module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap98.«98_3_1_1_Functor»

/-!
# The morphism of predeformation categories induced by a 2-Yoneda representative

An object `x` over `U` determines a 1-morphism `(Sch/U)_fppf ⟶ 𝒳`. Evaluating that
1-morphism on the predeformation category of the slice at a finite type point `u0`
with residue field `κ(u0)` yields a based functor over `ArtinianLocalAlgCat Λ κ(u0)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids (toFunctor fiberFunctor slice)
open FiberedCategoryOver.Groupoids.YonedaSlice

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

/-- The residue field `κ(u0)` of a point of a scheme `U` over `S`. -/
abbrev residueType {S : Scheme.{u}} (U : Over S) (u0 : U.left) : Type u :=
  IsLocalRing.ResidueField (U.left.presheaf.stalk u0)

/-- `residueType U u0` is the carrier of the residue field of `u0`. -/
theorem residueType_eq {S : Scheme.{u}} (U : Over S) (u0 : U.left) :
    residueType U u0 = U.left.residueField u0 :=
  sorry

/-- The morphism `Spec κ(u0) ⟶ S` obtained by composing the canonical residue-field
point of `u0` with `U ⟶ S`. -/
abbrev residuePointToS {S : Scheme.{u}} (U : Over S) (u0 : U.left) :
    Spec (CommRingCat.of (residueType U u0)) ⟶ S :=
  U.left.fromSpecResidueField u0 ≫ U.hom

/-- `residuePointToS` is the composite of `fromSpecResidueField` with `U.hom`. -/
theorem residuePointToS_eq {S : Scheme.{u}} (U : Over S) (u0 : U.left) :
    residuePointToS U u0 = U.left.fromSpecResidueField u0 ≫ U.hom :=
  sorry

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (U : Over S) (u0 : U.left)
variable [Algebra Λ (residueType U u0)]
variable [Module.Finite Λ (residueType U u0)]
variable (kToS : Spec (CommRingCat.of (residueType U u0)) ⟶ S)
variable [LocallyOfFiniteType kToS]
variable (h_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ (residueType U u0))) ≫ openImmersion =
      kToS)
variable (h_kToS : kToS = residuePointToS U u0)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x : X.p.Fiber U)

/-- The object of `(Sch/U)_fppf` associated to a morphism `Spec(k) ⟶ U` over `S`. -/
def residueFiberMk {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S) (U : Over S)
    (φ : Spec (CommRingCat.of k) ⟶ U.left) (hφ : φ ≫ U.hom = kToS) :
    (slice U).p.Fiber (Over.mk kToS) :=
  ⟨Over.mk (Over.homMk φ hφ : Over.mk kToS ⟶ U), rfl⟩

/-- `residueFiberMk` is the object of `Over U` given by `φ` as a morphism over `S`. -/
theorem residueFiberMk_spec {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S) (U : Over S)
    (φ : Spec (CommRingCat.of k) ⟶ U.left) (hφ : φ ≫ U.hom = kToS) :
    Fiber.fiberInclusion.obj (residueFiberMk kToS U φ hφ) =
      Over.mk (Over.homMk φ hφ : Over.mk kToS ⟶ U) :=
  sorry

/-- The object `u0` of `(Sch/U)_fppf` lying over the canonical residue-field point
`Spec κ(u0) ⟶ S`. -/
def residueFiber [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    (slice U).p.Fiber (Over.mk kToS) :=
  ⟨Over.mk (Over.homMk (U.left.fromSpecResidueField u0)
      h_kToS.symm : Over.mk kToS ⟶ U), rfl⟩

/-- `residueFiber` is the object of `Over U` given by the canonical residue-field
morphism of the finite type point `u0`. -/
theorem residueFiber_spec [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    Fiber.fiberInclusion.obj (residueFiber U u0 kToS h_kToS) =
      Over.mk (Over.homMk (U.left.fromSpecResidueField u0)
        h_kToS.symm : Over.mk kToS ⟶ U) :=
  sorry

/-- The pullback `x0` of `x` along the canonical residue-field point of `u0`,
obtained by evaluating the 2-Yoneda 1-morphism of `x` on `residueFiber`. -/
def residueObject [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    X.p.Fiber (Over.mk kToS) :=
  residueImage (representative x) (residueFiber U u0 kToS h_kToS)

/-- `residueObject` is the image of `residueFiber` under the fibre functor of the
2-Yoneda representative of `x`. -/
theorem residueObject_spec [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    residueObject U u0 kToS h_kToS X x =
      (fiberFunctor (representative x) (Over.mk kToS)).obj
        (residueFiber U u0 kToS h_kToS) :=
  sorry

/-- The based functor `ℱ_{(Sch/U)_fppf, κ(u0), u0} ⥤ᵇ ℱ_{𝒳, κ(u0), x0}` obtained by
applying predeformation functoriality to the 2-Yoneda representative of `x`. -/
def hatFunctor [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    predeformation openImmersion h_factor (slice U)
      (residueFiber U u0 kToS h_kToS) ⥤ᵇ
      predeformation openImmersion h_factor X
        (residueObject U u0 kToS h_kToS X x) :=
  map openImmersion h_factor (representative x) (residueFiber U u0 kToS h_kToS)

/-- The object map of `hatFunctor` keeps the Artinian base and applies the 2-Yoneda
representative of `x` to the target and the residue morphism. -/
def hatObj [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0]
    (ξ : Obj openImmersion kToS h_factor (slice U)
      (residueFiber U u0 kToS h_kToS)) :
    Obj openImmersion kToS h_factor X (residueObject U u0 kToS h_kToS X x) :=
  (hatFunctor openImmersion U u0 kToS h_factor h_kToS X x).obj ξ

/-- The morphism map of `hatFunctor` keeps the Artinian base homomorphism and applies
the 2-Yoneda representative of `x` to the reversed total-category arrow. -/
def hatHom [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0]
    {ξ η : Obj openImmersion kToS h_factor (slice U)
      (residueFiber U u0 kToS h_kToS)} (f : Hom ξ η) :
    Hom (hatObj openImmersion U u0 kToS h_factor h_kToS X x ξ)
      (hatObj openImmersion U u0 kToS h_factor h_kToS X x η) :=
  (hatFunctor openImmersion U u0 kToS h_factor h_kToS X x).map f

end AlgebraicGeometry.GroupoidsOver.Predeformation
