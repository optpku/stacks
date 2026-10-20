module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsSeparated f] [LocallyOfFiniteType f]
variable [IsSeparated g] [LocallyOfFiniteType g]

section assoc

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [IsSeparated h] [LocallyOfFiniteType h]

/-- `etaleLowerShriek` depends only on the underlying morphism, so it is
unchanged by reassociation of a triple composite. -/
theorem etaleLowerShriek_assoc :
    etaleLowerShriek ((f ≫ g) ≫ h) = etaleLowerShriek (f ≫ g ≫ h) :=
  sorry

/-- Left-then-bottom path of the associativity square: apply
`(etaleLowerShriekCompIso (f ≫ g) h).inv`, whisker
`(etaleLowerShriekCompIso f g).inv` on the right, then the functor
associator. -/
def etaleLowerShriekCompIso_assoc_left :
    etaleLowerShriek ((f ≫ g) ≫ h) ⟶
      etaleLowerShriek f ⋙ etaleLowerShriek g ⋙ etaleLowerShriek h :=
  (etaleLowerShriekCompIso (f ≫ g) h).inv ≫
    whiskerRight (etaleLowerShriekCompIso f g).inv (etaleLowerShriek h) ≫
    (associator (etaleLowerShriek f) (etaleLowerShriek g) (etaleLowerShriek h)).hom

/-- Top-then-right path of the associativity square: apply
`(etaleLowerShriekCompIso f (g ≫ h)).inv`, then whisker
`(etaleLowerShriekCompIso g h).inv` on the left. -/
def etaleLowerShriekCompIso_assoc_right :
    etaleLowerShriek (f ≫ g ≫ h) ⟶
      etaleLowerShriek f ⋙ etaleLowerShriek g ⋙ etaleLowerShriek h :=
  (etaleLowerShriekCompIso f (g ≫ h)).inv ≫
    whiskerLeft (etaleLowerShriek f) (etaleLowerShriekCompIso g h).inv

end assoc

section baseChange_vcomp

variable {X' Y' Z' : Scheme.{u}}
variable (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
variable (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
variable [IsSeparated f'] [LocallyOfFiniteType f']
variable [IsSeparated g'] [LocallyOfFiniteType g']

/-- Two-step path of the pasted base-change square: the composition
identification of `f` and `g`, then the lower base change of `g`, then the
upper base change of `f`, with functor associators. -/
def etaleLowerShriekCompIso_baseChange_vcomp_inner :
    etaleLowerShriek (f ≫ g) ⋙ etaleAbelianSheafPullback a ⟶
      etaleAbelianSheafPullback c ⋙ etaleLowerShriek f' ⋙ etaleLowerShriek g' :=
  whiskerRight (etaleLowerShriekCompIso f g).inv (etaleAbelianSheafPullback a) ≫
    (associator (etaleLowerShriek f) (etaleLowerShriek g)
        (etaleAbelianSheafPullback a)).hom ≫
    whiskerLeft (etaleLowerShriek f) (etaleLowerShriekBaseChange g a g' b h_lower) ≫
    (associator (etaleLowerShriek f) (etaleAbelianSheafPullback b)
        (etaleLowerShriek g')).inv ≫
    whiskerRight (etaleLowerShriekBaseChange f b f' c h_upper) (etaleLowerShriek g') ≫
    (associator (etaleAbelianSheafPullback c) (etaleLowerShriek f')
        (etaleLowerShriek g')).hom

/-- Outer path of the pasted base-change square: base change of `f ≫ g` along
the pasted cartesian square, then the composition identification of `f'` and
`g'`. -/
def etaleLowerShriekCompIso_baseChange_vcomp_outer :
    etaleLowerShriek (f ≫ g) ⋙ etaleAbelianSheafPullback a ⟶
      etaleAbelianSheafPullback c ⋙ etaleLowerShriek f' ⋙ etaleLowerShriek g' :=
  etaleLowerShriekBaseChange (f ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) ≫
    whiskerLeft (etaleAbelianSheafPullback c) (etaleLowerShriekCompIso f' g').inv

end baseChange_vcomp

/-- For three composable separated locally finite-type scheme morphisms, the
canonical composition isomorphisms for compact-support direct image satisfy
associativity after transport along reassociation of the composite. -/
theorem etaleLowerShriekCompIso_assoc
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    [IsSeparated h] [LocallyOfFiniteType h] :
    etaleLowerShriekCompIso_assoc_left f g h =
      eqToHom (etaleLowerShriek_assoc f g h) ≫
        etaleLowerShriekCompIso_assoc_right f g h :=
  sorry

/-- For two vertically pasted cartesian squares of schemes whose unprimed
vertical morphisms are separated and locally of finite type, the canonical
composition isomorphisms for compact-support direct image commute with base change. -/
theorem etaleLowerShriekCompIso_baseChange_vcomp
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
    (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g] :
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
    letI : IsSeparated f' :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_upper inferInstance
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_upper inferInstance
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
    letI : IsSeparated g' :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_lower inferInstance
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
    letI : LocallyOfFiniteType g' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_lower inferInstance
    etaleLowerShriekCompIso_baseChange_vcomp_outer f g f' g' a b c h_upper h_lower =
      etaleLowerShriekCompIso_baseChange_vcomp_inner f g f' g' a b c h_upper h_lower := by
  -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
  letI : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_upper inferInstance
  -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
  letI : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_upper inferInstance
  -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
  letI : IsSeparated g' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_lower inferInstance
  -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of the primed morphism from its unprimed morphism; it is not an additional assumption.
  letI : LocallyOfFiniteType g' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_lower inferInstance
  sorry

end AlgebraicGeometry.Scheme.Etale

end
