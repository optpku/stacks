module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import ReasLib.CategoryTheory.Inertia.Relative
public import stacks_project.Chap95.Example_95_17_1_Coproduct

/-!
# Comparison from the disjoint union of `[[X^g/G]]` into inertia of `[[X/G]]`

Pushing equivariant maps along the inclusion `X^g ⟶ X` and taking the torsor automorphism
of `g` produces a cartesian functor from the disjoint union into the inertia stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.QuotientStack.AbstractGroup
open AlgebraicGeometry.QuotientStack.FixedLocus
open AlgebraicGeometry.QuotientStack.InertiaCoprod
open scoped CategoryTheory.BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.InertiaCoprod

variable {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}

/-- Translation by `g` on an `underline(G)`-torsor, as an isomorphism of the underlying sheaf. -/
def torsorAutIso {U : Scheme.{u}} (P : Sheaf.Torsor (constantGroupSheaf U G)) (g : G) :
    P.carrier ≅ P.carrier where
  hom := torsorAut P g
  inv := torsorAut P g⁻¹
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Push an equivariant map into `X^g` along the inclusion `X^g ⟶ X`. -/
def includeφ (ρ : G →* Aut X) (g : G) {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    (φ : P.carrier ⟶ (restrict U).obj (toSheaf (ofOver (fixedLocus ρ g)))) :
    P.carrier ⟶ (restrict U).obj (toSheaf (ofOver X)) :=
  φ ≫ (restrict U).map (ofOverSheafMap (inclusion ρ g))

/-- Pushing along the inclusion is postcomposition with the sheaf map of the inclusion. -/
theorem includeφ_spec (ρ : G →* Aut X) (g : G) {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    (φ : P.carrier ⟶ (restrict U).obj (toSheaf (ofOver (fixedLocus ρ g)))) :
    includeφ ρ g φ = φ ≫ (restrict U).map (ofOverSheafMap (inclusion ρ g)) :=
  sorry

/-- The object of `[[X/G]]` obtained by composing `φ : P ⟶ X^g` with the inclusion `X^g ⟶ X`. -/
def includeObj (ρ : G →* Aut X) (g : G)
    (ξ : Obj (ofOverAut.comp (residual ρ g))) :
    Obj (ofOverAut.comp ρ) where
  U := ξ.U
  P := ξ.P
  φ := includeφ ρ g ξ.φ
  equivariant := sorry

/-- `includeObj` retains the underlying scheme and torsor. -/
theorem includeObj_spec (ρ : G →* Aut X) (g : G)
    (ξ : Obj (ofOverAut.comp (residual ρ g))) :
    (includeObj ρ g ξ).U = ξ.U ∧ (includeObj ρ g ξ).P = ξ.P :=
  sorry

/-- Push a morphism of `[[X^g/G]]` along the inclusion of the fixed locus. -/
def includeMap (ρ : G →* Aut X) (g : G)
    {ξ ξ' : Obj (ofOverAut.comp (residual ρ g))} (α : ξ ⟶ ξ') :
    includeObj ρ g ξ ⟶ includeObj ρ g ξ' where
  f := α.f
  g := α.g
  equivariant := sorry
  comm := sorry

/-- The underlying scheme map of `includeMap` is the original scheme map. -/
theorem includeMap_f (ρ : G →* Aut X) (g : G)
    {ξ ξ' : Obj (ofOverAut.comp (residual ρ g))} (α : ξ ⟶ ξ') :
    (includeMap ρ g α).f = α.f :=
  sorry

/-- Multiplication by `g` as an automorphism of an object of `[[X/G]]` over the identity on the
test scheme. -/
def mulHom {Y : AlgebraicSpace S} (σ : G →* Aut Y) (ξ : Obj σ) (g : G) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := torsorAutIso ξ.P g ≪≫ (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := sorry
  comm := sorry

/-- Multiplication by `g` as an element of `Aut ξ`. -/
def mulAut {Y : AlgebraicSpace S} (σ : G →* Aut Y) (ξ : Obj σ) (g : G) : Aut ξ where
  hom := mulHom σ ξ g
  inv := mulHom σ ξ g⁻¹
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The object map of the fold from `∐_g [[X^g/G]]` into the inertia of `[[X/G]]`. -/
def toInertiaObj (ρ : G →* Aut X) (ξ : CoprodObj ρ) :
    RelativeInertia (forget (ofOverAut.comp ρ)) where
  obj := includeObj ρ ξ.idx ξ.obj
  aut := mulAut (ofOverAut.comp ρ) (includeObj ρ ξ.idx ξ.obj) ξ.idx
  mapAut_eq_one := sorry

/-- The image object of `toInertiaObj` has the same test scheme as the source summand. -/
theorem toInertia_idx (ρ : G →* Aut X) (ξ : CoprodObj ρ) :
    (toInertiaObj ρ ξ).obj.U = ξ.obj.U :=
  sorry

/-- The image automorphism of `toInertiaObj` lies over the identity of the test scheme. -/
theorem toInertia_aut (ρ : G →* Aut X) (ξ : CoprodObj ρ) :
    (toInertiaObj ρ ξ).aut.hom.f = 𝟙 ξ.obj.U :=
  sorry

/-- The arrow map of the fold from `∐_g [[X^g/G]]` into the inertia of `[[X/G]]`. -/
def toInertiaMap (ρ : G →* Aut X) {ξ ξ' : CoprodObj ρ}
    (α : ξ ⟶ ξ') : toInertiaObj ρ ξ ⟶ toInertiaObj ρ ξ' :=
  match α with
  | CoprodHom.mk f =>
      RelativeInertia.homMk (forget (ofOverAut.comp ρ)) (includeMap ρ ξ.idx f) sorry

/-- The total functor of the fold `∐_g [[X^g/G]] ⟶ I_{[[X/G]]}`. -/
def toInertiaFunctor (ρ : G →* Aut X) :
    CoprodObj ρ ⥤ RelativeInertia (forget (ofOverAut.comp ρ)) where
  obj := toInertiaObj ρ
  map := toInertiaMap ρ
  map_id := sorry
  map_comp := sorry

/-- The cartesian comparison from the disjoint union of `[[X^g/G]]` into the inertia stack of
`[[X/G]]`. -/
def toInertia (ρ : G →* Aut X) :
    CartesianBasedFunctor (p ρ)
      (StackOver.Groupoids.inertia (stack (ofOverAut.comp ρ))).p :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedFunctor.ofFunctor (toInertiaFunctor ρ) sorry) sorry

/-- The underlying based functor of `toInertia`. -/
def toCartesian (ρ : G →* Aut X) :
    BasedCategory.ofFunctor (p ρ) ⥤ᵇ
      BasedCategory.ofFunctor
        (StackOver.Groupoids.inertia (stack (ofOverAut.comp ρ))).p :=
  (toInertia ρ).toBasedFunctor

/-- The underlying based functor of `toInertia` is `toCartesian`. -/
theorem toCartesian_eq (ρ : G →* Aut X) :
    (toInertia ρ).toBasedFunctor = toCartesian ρ :=
  sorry

end AlgebraicGeometry.QuotientStack.InertiaCoprod
