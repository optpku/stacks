module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# Sheaves for valuative covering families

This module defines the sheaf condition obtained by imposing the fixed-family
sheaf condition on every valuative covering family.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- A scheme presheaf satisfies the `V`-sheaf condition when it satisfies the
fixed-family sheaf condition for every `V` covering. -/
abbrev satisfiesVSheafProperty (F : Scheme.{u}ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {ι : Type w} {T : Scheme.{u}} (family : ι → Scheme.{u})
    (map : ∀ i, family i ⟶ T),
      IsVCovering T family map → satisfiesSheafPropertyForFamily F family map

/-- A `V` sheaf satisfies the fixed-family sheaf condition for every
`V`-covering family. -/
theorem satisfiesVSheafProperty.isSheafFor
    (hF : satisfiesVSheafProperty.{u, v, w} F)
    {ι : Type w} {T : Scheme.{u}} (family : ι → Scheme.{u})
    (map : ∀ i, family i ⟶ T) (hcover : IsVCovering T family map) :
    satisfiesSheafPropertyForFamily F family map := sorry

/-- The `V`-sheaf condition unfolds to sheafness for each `V`-covering
family. -/
theorem satisfiesVSheafProperty_iff (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    satisfiesVSheafProperty.{u, v, w} F ↔
      ∀ {ι : Type w} {T : Scheme.{u}} (family : ι → Scheme.{u})
        (map : ∀ i, family i ⟶ T),
          IsVCovering T family map → satisfiesSheafPropertyForFamily F family map := sorry

end AlgebraicGeometry
