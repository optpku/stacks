module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Beauville–Laszlo glueing of algebraic spaces

For a ring homomorphism `R → R'` and `f : R`, write `X = Spec R`,
`U = Spec R_f`, `X' = Spec R'`, and `U' = Spec R'_f`. The category
`Spaces(U ← U' → X')` is the categorical pullback of `Over.pullback`
along `U' ⟶ U` and along `U' ⟶ X'`. The canonical functor
`Spaces/X ⥤ Spaces(U ← U' → X')` sends `Y ⟶ X` to
`(U ×_X Y, U' ×_X Y, X' ×_X Y)` by base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- `X = Spec R` as an algebraic space over itself. -/
def space (R : Type u) [CommRing R] : AlgebraicSpace (Spec (CommRingCat.of R)) :=
  ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))

/-- `space R` is `ofOver` of the identity slice of `Spec R`. -/
theorem space_eq (R : Type u) [CommRing R] :
    space R = ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))) :=
  sorry

/-- `U = Spec R_f` as an algebraic space over `Spec R`. -/
def away {R : Type u} [CommRing R] (f : R) : AlgebraicSpace (Spec (CommRingCat.of R)) :=
  ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))

/-- `away f` is `ofOver` of `Spec.map` of `algebraMap R (Localization.Away f)`. -/
theorem away_eq {R : Type u} [CommRing R] (f : R) :
    away f =
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))) :=
  sorry

/-- `X' = Spec R'` as an algebraic space over `Spec R`. -/
def extension {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] :
    AlgebraicSpace (Spec (CommRingCat.of R)) :=
  ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

/-- `extension R'` is `ofOver` of `Spec.map` of `algebraMap R R'`. -/
theorem extension_eq {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] :
    extension R' =
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :=
  sorry

/-- `U' = Spec R'_f` as an algebraic space over `Spec R`, via the composite
`Spec R'_f ⟶ Spec R' ⟶ Spec R`. -/
def awayExtension {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    AlgebraicSpace (Spec (CommRingCat.of R)) :=
  ofOver
    (Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (algebraMap R R' f)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R'))))

/-- `awayExtension R' f` is `ofOver` of the composite structure morphism through `Spec R'`. -/
theorem awayExtension_eq {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) :
    awayExtension R' f =
      ofOver
        (Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (algebraMap R R' f)))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R R')))) :=
  sorry

/-- The structure morphism `U ⟶ X`. -/
def awayι {R : Type u} [CommRing R] (f : R) : away f ⟶ space R :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
    (Category.comp_id _)

/-- `awayι f` is `ofOverHomMk` of `Spec.map` of `algebraMap R (Localization.Away f)`. -/
theorem awayι_eq {R : Type u} [CommRing R] (f : R) :
    awayι f =
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
        (Category.comp_id _) :=
  sorry

/-- The structure morphism `X' ⟶ X`. -/
def extensionι {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] :
    extension R' ⟶ space R :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Category.comp_id _)

/-- `extensionι R'` is `ofOverHomMk` of `Spec.map` of `algebraMap R R'`. -/
theorem extensionι_eq {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] :
    extensionι R' =
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Category.comp_id _) :=
  sorry

/-- `Spec.map` of `Localization.awayMap` is compatible with the structure morphisms of
`U'` and `U` over `Spec R`. -/
theorem restrict_triangle {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) :
    Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap R R') f)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (algebraMap R R' f)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
  sorry

/-- The restriction morphism `U' ⟶ U`. -/
def restrict {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    awayExtension R' f ⟶ away f :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap R R') f)))
    (restrict_triangle R' f)

/-- `restrict R' f` is `ofOverHomMk` of `Spec.map` of `Localization.awayMap`. -/
theorem restrict_eq {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    restrict R' f =
      ofOverHomMk (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap R R') f)))
        (restrict_triangle R' f) :=
  sorry

/-- The structure morphism `U' ⟶ X'`. -/
def awayExtensionι {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    awayExtension R' f ⟶ extension R' :=
  ofOverHomMk
    (Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (algebraMap R R' f))))) rfl

/-- `awayExtensionι R' f` is `ofOverHomMk` of `Spec.map` of `algebraMap R' R'_f`. -/
theorem awayExtensionι_eq {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) :
    awayExtensionι R' f =
      ofOverHomMk
        (Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (algebraMap R R' f)))))
        rfl :=
  sorry

/-- The Spec square `U' ⟶ U ⟶ X` equals `U' ⟶ X' ⟶ X`. -/
theorem square_commutes {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) :
    restrict R' f ≫ awayι f = awayExtensionι R' f ≫ extensionι R' :=
  sorry

/-- The category `Spaces(U ← U' → X')` of triples `(V, Y', φ)` with `V` an algebraic
space over `U`, `Y'` an algebraic space over `X'`, and
`φ : V ×_U U' ≅ Y' ×_{X'} U'`. -/
abbrev category {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :=
  CategoricalPullback (Over.pullback (restrict R' f)) (Over.pullback (awayExtensionι R' f))

/-- The left objects of pullback along the two composites `U' ⟶ X` have isomorphic
structure morphisms to `U'`. -/
theorem canOverlap_iso_w {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) (Y : Over (space R)) :
    (pullback.congrHom (rfl : Y.hom = Y.hom) (square_commutes R' f)).hom ≫
        ((Over.pullback (awayExtensionι R' f ≫ extensionι R')).obj Y).hom =
      ((Over.pullback (restrict R' f ≫ awayι f)).obj Y).hom :=
  sorry

/-- Naturality of the comparison isomorphisms of pullbacks along the two composites
`U' ⟶ X`. -/
theorem canOverlap_naturality {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) {Y₁ Y₂ : Over (space R)} (g : Y₁ ⟶ Y₂) :
    (Over.pullback (restrict R' f ≫ awayι f)).map g ≫
        (Over.isoMk (pullback.congrHom rfl (square_commutes R' f))
          (canOverlap_iso_w R' f Y₂)).hom =
      (Over.isoMk (pullback.congrHom rfl (square_commutes R' f))
          (canOverlap_iso_w R' f Y₁)).hom ≫
        (Over.pullback (awayExtensionι R' f ≫ extensionι R')).map g :=
  sorry

/-- Comparison of `Over.pullback` along the two composites `U' ⟶ X`. -/
def canOverlap {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    Over.pullback (restrict R' f ≫ awayι f) ≅
      Over.pullback (awayExtensionι R' f ≫ extensionι R') :=
  NatIso.ofComponents
    (fun Y ↦
      Over.isoMk (pullback.congrHom rfl (square_commutes R' f)) (canOverlap_iso_w R' f Y))
    (canOverlap_naturality R' f)

/-- The canonical isomorphism `(U ×_X Y) ×_U U' ≅ (X' ×_X Y) ×_{X'} U'`. -/
def can {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    Over.pullback (awayι f) ⋙ Over.pullback (restrict R' f) ≅
      Over.pullback (extensionι R') ⋙ Over.pullback (awayExtensionι R' f) :=
  (Over.pullbackComp (restrict R' f) (awayι f)).symm ≪≫
    canOverlap R' f ≪≫ Over.pullbackComp (awayExtensionι R' f) (extensionι R')

/-- The canonical functor `Spaces/X ⥤ Spaces(U ← U' → X')` sending `Y ⟶ X` to
`(U ×_X Y, X' ×_X Y, can)`. -/
def functor {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    Over (space R) ⥤ category R' f :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (Over.pullback (restrict R' f)) (Over.pullback (awayExtensionι R' f))
      (Over (space R))).obj
    { fst := Over.pullback (awayι f)
      snd := Over.pullback (extensionι R')
      iso := can R' f }

/-- An object of `Spaces(U ← U' → X')` from a triple `(V, Y', φ)`. -/
def mk {R : Type u} {R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {f : R}
    {V : Over (away f)} {Y' : Over (extension R')}
    (φ : (Over.pullback (restrict R' f)).obj V ≅
      (Over.pullback (awayExtensionι R' f)).obj Y') :
    category R' f :=
  ⟨V, Y', φ⟩

/-- The overlap space `V'` of an object of `Spaces(U ← U' → X')`, recovered as the
pullback of `V` along `U' ⟶ U`. -/
def overlap {R : Type u} {R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {f : R}
    (obj : category R' f) : Over (awayExtension R' f) :=
  (Over.pullback (restrict R' f)).obj obj.fst

/-- The first component of the canonical glueing functor is base change along `U ⟶ X`. -/
theorem obj_fst {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    (Y : Over (space R)) :
    ((functor R' f).obj Y).fst = (Over.pullback (awayι f)).obj Y :=
  sorry

/-- The second component of the canonical glueing functor is base change along `X' ⟶ X`. -/
theorem obj_snd {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    (Y : Over (space R)) :
    ((functor R' f).obj Y).snd = (Over.pullback (extensionι R')).obj Y :=
  sorry

/-- The structural isomorphism of the canonical glueing functor is the component of `can`. -/
theorem obj_iso {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    (Y : Over (space R)) :
    ((functor R' f).obj Y).iso = (can R' f).app Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
