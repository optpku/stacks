module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Projection
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Constructors
import Mathlib.Tactic.CrossRefAttribute

/-!
# Endpoint projections after mapping bundled cospans

Componentwise mapping of bundled cospans commutes with each vertex projection up to a canonical
strong transformation.  All three transformations have identity object components; their
naturality is the standard right-unitor/left-unitor comparison on the corresponding mapped
vertex morphism.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.Cospan

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']

/-- Naturality of the comparison between mapping a cospan and then taking its left endpoint and
taking the left endpoint before applying the ambient pseudofunctor. -/
def map.leftProjection.naturalityIso (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map P).comp (leftProjection B')).map psi ≫ 𝟙 (P.obj T.left) ≅
      𝟙 (P.obj S.left) ≫ ((leftProjection B).comp P).map psi :=
  ρ_ (P.map (Hom.left psi)) ≪≫ (λ_ (P.map (Hom.left psi))).symm

/-- Naturality of the comparison between mapping a cospan and then taking its right endpoint and
taking the right endpoint before applying the ambient pseudofunctor. -/
def map.rightProjection.naturalityIso (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map P).comp (rightProjection B')).map psi ≫ 𝟙 (P.obj T.right) ≅
      𝟙 (P.obj S.right) ≫ ((rightProjection B).comp P).map psi :=
  ρ_ (P.map (Hom.right psi)) ≪≫ (λ_ (P.map (Hom.right psi))).symm

/-- Naturality of the comparison between mapping a cospan and then taking its common target and
taking the common target before applying the ambient pseudofunctor. -/
def map.baseProjection.naturalityIso (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map P).comp (baseProjection B')).map psi ≫ 𝟙 (P.obj T.base) ≅
      𝟙 (P.obj S.base) ≫ ((baseProjection B).comp P).map psi :=
  ρ_ (P.map (Hom.base psi)) ≪≫ (λ_ (P.map (Hom.base psi))).symm

namespace Implementation.MapProjection

/-- The left-projection comparison is natural in cospan `2`-morphisms. -/
private theorem leftNaturality₂ (P : B ⥤ᵖ B') :
    ∀ {S T : Cospan B} {psi phi : S ⟶ T} (Gamma : psi ⟶ phi),
      ((map P).comp (leftProjection B')).map₂ Gamma ▷ 𝟙 (P.obj T.left) ≫
          (map.leftProjection.naturalityIso P phi).hom =
        (map.leftProjection.naturalityIso P psi).hom ≫
          𝟙 (P.obj S.left) ◁ ((leftProjection B).comp P).map₂ Gamma := sorry

/-- The left-projection comparison is compatible with identity `1`-morphisms. -/
private theorem leftId (P : B ⥤ᵖ B') :
    ∀ S : Cospan B,
      (map.leftProjection.naturalityIso P (𝟙 S)).hom ≫
          𝟙 (P.obj S.left) ◁ (((leftProjection B).comp P).mapId S).hom =
        (((map P).comp (leftProjection B')).mapId S).hom ▷
            𝟙 (P.obj S.left) ≫
          (λ_ (𝟙 (P.obj S.left))).hom ≫
          (ρ_ (𝟙 (P.obj S.left))).inv := sorry

/-- The left-projection comparison is compatible with composition of `1`-morphisms. -/
private theorem leftComp (P : B ⥤ᵖ B') :
    ∀ {R S T : Cospan B} (psi : R ⟶ S) (phi : S ⟶ T),
      (map.leftProjection.naturalityIso P (psi ≫ phi)).hom ≫
          𝟙 (P.obj R.left) ◁
            (((leftProjection B).comp P).mapComp psi phi).hom =
        (((map P).comp (leftProjection B')).mapComp psi phi).hom ▷
            𝟙 (P.obj T.left) ≫
          (α_ _ _ _).hom ≫
          ((map P).comp (leftProjection B')).map psi ◁
            (map.leftProjection.naturalityIso P phi).hom ≫
          (α_ _ _ _).inv ≫
          (map.leftProjection.naturalityIso P psi).hom ▷
            ((leftProjection B).comp P).map phi ≫
          (α_ _ _ _).hom := sorry

/-- The right-projection comparison is natural in cospan `2`-morphisms. -/
private theorem rightNaturality₂ (P : B ⥤ᵖ B') :
    ∀ {S T : Cospan B} {psi phi : S ⟶ T} (Gamma : psi ⟶ phi),
      ((map P).comp (rightProjection B')).map₂ Gamma ▷ 𝟙 (P.obj T.right) ≫
          (map.rightProjection.naturalityIso P phi).hom =
        (map.rightProjection.naturalityIso P psi).hom ≫
          𝟙 (P.obj S.right) ◁ ((rightProjection B).comp P).map₂ Gamma := sorry

/-- The right-projection comparison is compatible with identity `1`-morphisms. -/
private theorem rightId (P : B ⥤ᵖ B') :
    ∀ S : Cospan B,
      (map.rightProjection.naturalityIso P (𝟙 S)).hom ≫
          𝟙 (P.obj S.right) ◁ (((rightProjection B).comp P).mapId S).hom =
        (((map P).comp (rightProjection B')).mapId S).hom ▷
            𝟙 (P.obj S.right) ≫
          (λ_ (𝟙 (P.obj S.right))).hom ≫
          (ρ_ (𝟙 (P.obj S.right))).inv := sorry

/-- The right-projection comparison is compatible with composition of `1`-morphisms. -/
private theorem rightComp (P : B ⥤ᵖ B') :
    ∀ {R S T : Cospan B} (psi : R ⟶ S) (phi : S ⟶ T),
      (map.rightProjection.naturalityIso P (psi ≫ phi)).hom ≫
          𝟙 (P.obj R.right) ◁
            (((rightProjection B).comp P).mapComp psi phi).hom =
        (((map P).comp (rightProjection B')).mapComp psi phi).hom ▷
            𝟙 (P.obj T.right) ≫
          (α_ _ _ _).hom ≫
          ((map P).comp (rightProjection B')).map psi ◁
            (map.rightProjection.naturalityIso P phi).hom ≫
          (α_ _ _ _).inv ≫
          (map.rightProjection.naturalityIso P psi).hom ▷
            ((rightProjection B).comp P).map phi ≫
          (α_ _ _ _).hom := sorry

/-- The base-projection comparison is natural in cospan `2`-morphisms. -/
private theorem baseNaturality₂ (P : B ⥤ᵖ B') :
    ∀ {S T : Cospan B} {psi phi : S ⟶ T} (Gamma : psi ⟶ phi),
      ((map P).comp (baseProjection B')).map₂ Gamma ▷ 𝟙 (P.obj T.base) ≫
          (map.baseProjection.naturalityIso P phi).hom =
        (map.baseProjection.naturalityIso P psi).hom ≫
          𝟙 (P.obj S.base) ◁ ((baseProjection B).comp P).map₂ Gamma := sorry

/-- The base-projection comparison is compatible with identity `1`-morphisms. -/
private theorem baseId (P : B ⥤ᵖ B') :
    ∀ S : Cospan B,
      (map.baseProjection.naturalityIso P (𝟙 S)).hom ≫
          𝟙 (P.obj S.base) ◁ (((baseProjection B).comp P).mapId S).hom =
        (((map P).comp (baseProjection B')).mapId S).hom ▷
            𝟙 (P.obj S.base) ≫
          (λ_ (𝟙 (P.obj S.base))).hom ≫
          (ρ_ (𝟙 (P.obj S.base))).inv := sorry

/-- The base-projection comparison is compatible with composition of `1`-morphisms. -/
private theorem baseComp (P : B ⥤ᵖ B') :
    ∀ {R S T : Cospan B} (psi : R ⟶ S) (phi : S ⟶ T),
      (map.baseProjection.naturalityIso P (psi ≫ phi)).hom ≫
          𝟙 (P.obj R.base) ◁
            (((baseProjection B).comp P).mapComp psi phi).hom =
        (((map P).comp (baseProjection B')).mapComp psi phi).hom ▷
            𝟙 (P.obj T.base) ≫
          (α_ _ _ _).hom ≫
          ((map P).comp (baseProjection B')).map psi ◁
            (map.baseProjection.naturalityIso P phi).hom ≫
          (α_ _ _ _).inv ≫
          (map.baseProjection.naturalityIso P psi).hom ▷
            ((baseProjection B).comp P).map phi ≫
          (α_ _ _ _).hom := sorry

end Implementation.MapProjection

/-- Componentwise mapping followed by the left-endpoint projection is canonically strongly
transformed to the left-endpoint projection followed by the ambient pseudofunctor. -/
@[stacks 0040 "left projection comparison for mapping bundled cospans"]
def map.leftProjection (P : B ⥤ᵖ B') :
    Pseudofunctor.StrongTrans
      ((map P).comp (leftProjection B')) ((leftProjection B).comp P) where
  app S := 𝟙 (P.obj S.left)
  naturality psi := map.leftProjection.naturalityIso P psi
  naturality_naturality := Implementation.MapProjection.leftNaturality₂ P
  naturality_id := Implementation.MapProjection.leftId P
  naturality_comp := Implementation.MapProjection.leftComp P

/-- Componentwise mapping followed by the right-endpoint projection is canonically strongly
transformed to the right-endpoint projection followed by the ambient pseudofunctor. -/
@[stacks 0040 "right projection comparison for mapping bundled cospans"]
def map.rightProjection (P : B ⥤ᵖ B') :
    Pseudofunctor.StrongTrans
      ((map P).comp (rightProjection B')) ((rightProjection B).comp P) where
  app S := 𝟙 (P.obj S.right)
  naturality psi := map.rightProjection.naturalityIso P psi
  naturality_naturality := Implementation.MapProjection.rightNaturality₂ P
  naturality_id := Implementation.MapProjection.rightId P
  naturality_comp := Implementation.MapProjection.rightComp P

/-- Componentwise mapping followed by the common-target projection is canonically strongly
transformed to the common-target projection followed by the ambient pseudofunctor. -/
@[stacks 0040 "base projection comparison for mapping bundled cospans"]
def map.baseProjection (P : B ⥤ᵖ B') :
    Pseudofunctor.StrongTrans
      ((map P).comp (baseProjection B')) ((baseProjection B).comp P) where
  app S := 𝟙 (P.obj S.base)
  naturality psi := map.baseProjection.naturalityIso P psi
  naturality_naturality := Implementation.MapProjection.baseNaturality₂ P
  naturality_id := Implementation.MapProjection.baseId P
  naturality_comp := Implementation.MapProjection.baseComp P

/-- The left-projection comparison is pointwise an equivalence. -/
def map.leftProjection.pointwiseEquivalence (P : B ⥤ᵖ B') :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (map.leftProjection P) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun S ↦ Bicategory.Equivalence.id (P.obj S.left)) (fun _ ↦ Iso.refl _)

/-- The right-projection comparison is pointwise an equivalence. -/
def map.rightProjection.pointwiseEquivalence (P : B ⥤ᵖ B') :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (map.rightProjection P) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun S ↦ Bicategory.Equivalence.id (P.obj S.right)) (fun _ ↦ Iso.refl _)

/-- The base-projection comparison is pointwise an equivalence. -/
def map.baseProjection.pointwiseEquivalence (P : B ⥤ᵖ B') :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (map.baseProjection P) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun S ↦ Bicategory.Equivalence.id (P.obj S.base)) (fun _ ↦ Iso.refl _)

end CategoryTheory.Bicategory.Cospan
