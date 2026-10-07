module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import ReasLib.Algebra.Group.Units.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local morphisms of commutative-ring sheaves

The reusable property is objectwise reflection of units.  The cartesian units-square
formulation is exposed as an equivalent view, so geometric APIs do not need their own long
set-theoretic pullback definitions.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.LocalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪₁ 𝒪₂ : Sheaf J CommRingCat.{w}}

/-- A morphism of commutative-ring sheaves is local when every map on sections reflects units. -/
class IsLocal (f : 𝒪₁ ⟶ 𝒪₂) : Prop where
  app (U : Cᵒᵖ) : IsLocalHom (f.hom.app U).hom

/-- Locality of a sheaf morphism supplies locality of each component to typeclass search. -/
instance app_isLocal (f : 𝒪₁ ⟶ 𝒪₂) [IsLocal f] (U : Cᵒᵖ) :
    IsLocalHom (f.hom.app U).hom :=
  IsLocal.app U

/-- The units square of a sheaf morphism is objectwise cartesian. -/
def UnitsSquareCartesian (f : 𝒪₁ ⟶ 𝒪₂) : Prop :=
  ∀ U : Cᵒᵖ, Units.Square.IsCartesian (f.hom.app U).hom.toMonoidHom

/-- Lemma 18.40.8 (04H9), sheaf-level core: objectwise cartesianness of the units square is
equivalent to locality of the morphism. -/
@[stacks 04H9 "objectwise units-square criterion"]
theorem unitsSquareCartesian_iff_isLocal (f : 𝒪₁ ⟶ 𝒪₂) :
    UnitsSquareCartesian f ↔ IsLocal f := sorry

end CategoryTheory.Sheaf.LocalHom
