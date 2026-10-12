/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0

variable {X Y Z : Scheme.{u}}

/-- Canonical derived pullback values kill the triangulated Grothendieck relations. -/
theorem relations_le_ker_pullback (f : X ⟶ Y) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun K ↦
        TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K)).ker := sorry

/-- The additive pullback induced by canonical derived pullback on perfect complexes. -/
noncomputable def pullbackAdd (f : X ⟶ Y) : K0 Y →+ K0 X :=
  TriangulatedK0.lift
    (fun K ↦ TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K))
    (relations_le_ker_pullback f)

/-- The additive pullback sends a perfect generator to its derived pullback. -/
theorem pullbackAdd_of (f : X ⟶ Y)
    (K : RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace)) :
    pullbackAdd f (TriangulatedK0.of K) =
      TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K) := sorry

/-- The additive pullback preserves the multiplicative unit in perfect-complex `K₀`. -/
theorem pullbackAdd_map_one (f : X ⟶ Y) :
    pullbackAdd f (1 : K0 Y) = 1 := sorry

/-- The additive pullback preserves multiplication in perfect-complex `K₀`. -/
theorem pullbackAdd_map_mul (f : X ⟶ Y) (a b : K0 Y) :
    pullbackAdd f (a * b) = pullbackAdd f a * pullbackAdd f b := sorry

/-- Pullback on perfect-complex Grothendieck groups. -/
noncomputable def pullback (f : X ⟶ Y) : K0 Y →+* K0 X :=
  { pullbackAdd f with
    map_one' := pullbackAdd_map_one f
    map_mul' := pullbackAdd_map_mul f }

/-- Pullback sends the class of a perfect complex to the class of its derived pullback. -/
theorem pullback_of (f : X ⟶ Y)
    (K : RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace)) :
    pullback f (TriangulatedK0.of K) =
      TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K) := sorry

/-- Pullback along the identity morphism is the identity on perfect-complex `K₀`. -/
theorem pullback_id (X : Scheme.{u}) :
    pullback (𝟙 X) = RingHom.id (K0 X) := sorry

/-- Pullback is contravariantly functorial under composition. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := sorry

end AlgebraicGeometry.Scheme.K0
