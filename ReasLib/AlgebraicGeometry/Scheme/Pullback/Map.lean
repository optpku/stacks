module

public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/-- The canonical comparison morphism from the pullback over an étale
neighbourhood to the original pullback. -/
noncomputable def baseChangeMap {X Y V V' : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (e : V' ⟶ V) :
    pullback f (e ≫ g) ⟶ pullback f g :=
  pullback.map f (e ≫ g) f g (𝟙 X) e (𝟙 Y)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    (Category.comp_id (e ≫ g))

/-- The first projection of `baseChangeMap` is the pullback projection of the
base-changed morphism. -/
theorem baseChangeMap_fst {X Y V V' : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (e : V' ⟶ V) :
    baseChangeMap f g e ≫ pullback.fst f g =
      pullback.fst f (e ≫ g) := sorry

/-- The second projection of `baseChangeMap` factors through the neighbourhood
morphism. -/
theorem baseChangeMap_snd {X Y V V' : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (e : V' ⟶ V) :
    baseChangeMap f g e ≫ pullback.snd f g =
      pullback.snd f (e ≫ g) ≫ e := sorry

end AlgebraicGeometry.Scheme.Pullback
