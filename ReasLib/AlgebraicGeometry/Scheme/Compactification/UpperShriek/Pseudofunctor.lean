module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Composition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete

/-!
# The upper-shriek pseudofunctor

This module packages coherent explicit choices of compactifications and bounded-below
right-adjoint models into a contravariant `Cat`-valued pseudofunctor.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open Compactification.Of

/-- An explicit coherent choice of the compactifications, bounded-below models, and
comparison isomorphisms used by the upper-shriek construction over `S`.

The choice is an ordinary parameter rather than a typeclass because its compactifications
and right-adjoint models are noncanonical. -/
structure UpperShriekAssignment (S : Scheme.{u}) [IsNoetherian S] where
  /-- The compactification selected for each finite-type separated morphism. -/
  compactification {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    Compactification.Of Y.obj.left (Over.mk f.hom.left)
  /-- The comparison system relating all compactifications of each morphism. -/
  comparisonSystem {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    UpperShriekComparisonSystem f
  /-- The selected bounded-below upper-shriek functor. -/
  map {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left
  /-- The selected functor is the upper-shriek functor arising from the selected
  compactification and bounded-below model. -/
  map_spec {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    map f = upperShriek f (compactification f)
      ((comparisonSystem f).model (compactification f)).plus
  /-- Compatible compactification and right-adjoint data for each composable pair. -/
  compChoice {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    UpperShriekCompChoice f g
  /-- The selected identity comparison for upper-shriek. -/
  mapId (X : FiniteTypeSeparatedOver S) :
    map (𝟙 X) ≅ Functor.id (DerivedQCoh.Plus X.obj.left)
  /-- The selected composition comparison `(f ≫ g) ! ≅ g ! ⋙ f !`. -/
  mapComp {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ map g ⋙ map f
  /-- The selected compositor is the canonical comparison obtained from its compatible
  compactification choice and the comparison systems of its three morphisms. -/
  mapComp_spec {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapComp f g =
      eqToIso (map_spec (f ≫ g)) ≪≫
        (comparisonSystem (f ≫ g)).iso
          (compactification (f ≫ g))
          (Compactification.Of.comp f g (compChoice f g).P_g (compChoice f g).P_bar)
          ((comparisonSystem (f ≫ g)).model (compactification (f ≫ g)))
          (compChoice f g).A_fg ≪≫
        (compChoice f g).compIso f g ≪≫
        Functor.isoWhiskerRight
          ((comparisonSystem g).iso (compChoice f g).P_g (compactification g)
              (compChoice f g).A_g
              ((comparisonSystem g).model (compactification g)) ≪≫
            eqToIso (map_spec g).symm)
          (upperShriek f (compChoice f g).P_f (compChoice f g).A_f.plus) ≪≫
        Functor.isoWhiskerLeft (map g)
          ((comparisonSystem f).iso (compChoice f g).P_f (compactification f)
              (compChoice f g).A_f
              ((comparisonSystem f).model (compactification f)) ≪≫
            eqToIso (map_spec f).symm)
  /-- The identity and composition comparisons obey the left-unit coherence equation. -/
  map₂_leftUnitor {X Y : (FiniteTypeSeparatedOver S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (mapComp f.unop (𝟙 X).unop)).hom ≫
        (Cat.Hom.isoMk (mapId (unop X))).hom ▷ (map f.unop).toCatHom ≫
      (λ_ (map f.unop).toCatHom).hom =
        eqToHom (congrArg (fun k ↦ (map k.unop).toCatHom) (Category.id_comp f))
  /-- The identity and composition comparisons obey the right-unit coherence equation. -/
  map₂_rightUnitor {X Y : (FiniteTypeSeparatedOver S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (mapComp (𝟙 Y).unop f.unop)).hom ≫
        (map f.unop).toCatHom ◁ (Cat.Hom.isoMk (mapId (unop Y))).hom ≫
      (ρ_ (map f.unop).toCatHom).hom =
        eqToHom (congrArg (fun k ↦ (map k.unop).toCatHom) (Category.comp_id f))

namespace UpperShriekAssignment

/-- Construct an upper-shriek assignment from explicit compactification, comparison,
functor, unit, and compositor data satisfying the defining specifications. -/
def of {S : Scheme.{u}} [IsNoetherian S]
    (compactification : {X Y : FiniteTypeSeparatedOver S} → (f : X ⟶ Y) →
      Compactification.Of Y.obj.left (Over.mk f.hom.left))
    (comparisonSystem : {X Y : FiniteTypeSeparatedOver S} → (f : X ⟶ Y) →
      UpperShriekComparisonSystem f)
    (map : {X Y : FiniteTypeSeparatedOver S} → (f : X ⟶ Y) →
      DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left)
    (map_spec : ∀ {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y),
      map f = upperShriek f (compactification f)
        ((comparisonSystem f).model (compactification f)).plus)
    (compChoice : {X Y Z : FiniteTypeSeparatedOver S} →
      (f : X ⟶ Y) → (g : Y ⟶ Z) → UpperShriekCompChoice f g)
    (mapId : (X : FiniteTypeSeparatedOver S) →
      map (𝟙 X) ≅ Functor.id (DerivedQCoh.Plus X.obj.left))
    (mapComp : {X Y Z : FiniteTypeSeparatedOver S} → (f : X ⟶ Y) → (g : Y ⟶ Z) →
      map (f ≫ g) ≅ map g ⋙ map f)
    (mapComp_spec : ∀ {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z),
      mapComp f g =
        eqToIso (map_spec (f ≫ g)) ≪≫
          (comparisonSystem (f ≫ g)).iso (compactification (f ≫ g))
            (Compactification.Of.comp f g (compChoice f g).P_g (compChoice f g).P_bar)
            ((comparisonSystem (f ≫ g)).model (compactification (f ≫ g)))
            (compChoice f g).A_fg ≪≫
          (compChoice f g).compIso f g ≪≫
          Functor.isoWhiskerRight
            ((comparisonSystem g).iso (compChoice f g).P_g (compactification g)
                (compChoice f g).A_g ((comparisonSystem g).model (compactification g)) ≪≫
              eqToIso (map_spec g).symm)
            (upperShriek f (compChoice f g).P_f (compChoice f g).A_f.plus) ≪≫
          Functor.isoWhiskerLeft (map g)
            ((comparisonSystem f).iso (compChoice f g).P_f (compactification f)
                (compChoice f g).A_f ((comparisonSystem f).model (compactification f)) ≪≫
              eqToIso (map_spec f).symm))
    (map₂_leftUnitor : ∀ {X Y : (FiniteTypeSeparatedOver S)ᵒᵖ} (f : X ⟶ Y),
      (Cat.Hom.isoMk (mapComp f.unop (𝟙 X).unop)).hom ≫
          (Cat.Hom.isoMk (mapId (unop X))).hom ▷ (map f.unop).toCatHom ≫
        (λ_ (map f.unop).toCatHom).hom =
          eqToHom (congrArg (fun k ↦ (map k.unop).toCatHom) (Category.id_comp f)))
    (map₂_rightUnitor : ∀ {X Y : (FiniteTypeSeparatedOver S)ᵒᵖ} (f : X ⟶ Y),
      (Cat.Hom.isoMk (mapComp (𝟙 Y).unop f.unop)).hom ≫
          (map f.unop).toCatHom ◁ (Cat.Hom.isoMk (mapId (unop Y))).hom ≫
        (ρ_ (map f.unop).toCatHom).hom =
          eqToHom (congrArg (fun k ↦ (map k.unop).toCatHom) (Category.comp_id f))) :
    UpperShriekAssignment S where
  compactification := compactification
  comparisonSystem := comparisonSystem
  map := map
  map_spec := map_spec
  compChoice := compChoice
  mapId := mapId
  mapComp := mapComp
  mapComp_spec := mapComp_spec
  map₂_leftUnitor := map₂_leftUnitor
  map₂_rightUnitor := map₂_rightUnitor

/-- For three composable morphisms, the two composites of the canonical upper-shriek
composition comparisons agree. -/
theorem mapComp_assoc
    {S : Scheme.{u}} [IsNoetherian S] (D : UpperShriekAssignment S)
    {X₀ X₁ X₂ X₃ : (FiniteTypeSeparatedOver S)ᵒᵖ}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (Cat.Hom.isoMk (D.mapComp h.unop (f ≫ g).unop)).hom ≫
        (Cat.Hom.isoMk (D.mapComp g.unop f.unop)).hom ▷ (D.map h.unop).toCatHom ≫
      (α_ (D.map f.unop).toCatHom (D.map g.unop).toCatHom
        (D.map h.unop).toCatHom).hom ≫
      (D.map f.unop).toCatHom ◁ (Cat.Hom.isoMk (D.mapComp h.unop g.unop)).inv ≫
      (Cat.Hom.isoMk (D.mapComp (g ≫ h).unop f.unop)).inv =
        eqToHom (congrArg (fun k ↦ (D.map k.unop).toCatHom)
          (Category.assoc f g h)) := sorry

/-- A coherent upper-shriek assignment determines the contravariant `Cat`-valued
pseudofunctor on finite-type separated schemes over `S`. -/
noncomputable def pseudofunctor
    {S : Scheme.{u}} [IsNoetherian S] (D : UpperShriekAssignment S) :
    LocallyDiscrete (FiniteTypeSeparatedOver S)ᵒᵖ ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (DerivedQCoh.Plus X.unop.obj.left))
    (fun f ↦ (D.map f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (D.mapId (unop X)))
    (fun f g ↦ Cat.Hom.isoMk (D.mapComp g.unop f.unop))
    D.mapComp_assoc D.map₂_leftUnitor D.map₂_rightUnitor

/-- The value of the upper-shriek pseudofunctor at `X` is the bounded-below derived
category of quasicoherent modules on `X`. -/
theorem pseudofunctor_obj
    {S : Scheme.{u}} [IsNoetherian S] (D : UpperShriekAssignment S)
    (X : FiniteTypeSeparatedOver S) :
    D.pseudofunctor.obj (LocallyDiscrete.mk (op X)) =
      Cat.of (DerivedQCoh.Plus X.obj.left) := sorry

/-- The action of the upper-shriek pseudofunctor on `f` is the selected upper-shriek
functor `D.map f`. -/
theorem pseudofunctor_map
    {S : Scheme.{u}} [IsNoetherian S] (D : UpperShriekAssignment S)
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    (D.pseudofunctor.map f.op.toLoc).toFunctor = D.map f := sorry

/-- The identity comparison of the upper-shriek pseudofunctor is the selected unit
isomorphism. -/
theorem pseudofunctor_mapId
    {S : Scheme.{u}} [IsNoetherian S] (D : UpperShriekAssignment S)
    (X : FiniteTypeSeparatedOver S) :
    Cat.Hom.toNatIso (D.pseudofunctor.mapIdOp X) = D.mapId X := sorry

/-- The composition comparison of the upper-shriek pseudofunctor is the canonical
comparison `(f ≫ g) ! ≅ g ! ⋙ f !` selected by `D`. -/
theorem pseudofunctor_mapComp
    {S : Scheme.{u}} [IsNoetherian S] (D : UpperShriekAssignment S)
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Cat.Hom.toNatIso (D.pseudofunctor.mapCompOp g f) = D.mapComp f g := sorry

end UpperShriekAssignment

end AlgebraicGeometry.Scheme
