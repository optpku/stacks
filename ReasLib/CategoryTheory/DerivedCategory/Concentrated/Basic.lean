/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Objects Concentrated in One Degree

This module models the objects of a derived category concentrated in a fixed
degree as a full subcategory.  The fully faithful `singleFunctor` identifies
the abelian category with this subcategory through its essential image.

The non-Prop data below are assembled from Mathlib's `Functor.toEssImage`,
`ObjectProperty.fullSubcategoryCongr`, equivalence counit, and
`singleFunctorCompHomologyFunctorIso`.  The proof debt is confined to the
essential-image identification and the naturality and normalization statements;
in particular, no public objectwise `Classical.choice` owns the resulting
isomorphisms.
-/

open CategoryTheory
open DerivedCategory.TStructure

universe w v u

noncomputable section

namespace CategoryTheory.DerivedCategory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The property of derived objects whose homology is concentrated in degree `n`. -/
@[stacks 08J5]
def concentrated (n : ℤ) : ObjectProperty (DerivedCategory 𝒜) :=
  t.le n ⊓ t.ge n

/-- The full subcategory of derived objects concentrated in degree `n`. -/
@[stacks 08J5]
abbrev Concentrated (n : ℤ) :=
  (concentrated 𝒜 n).FullSubcategory

/-- Membership in `concentrated 𝒜 n` is the conjunction of the two canonical
`t`-structure bounds in degree `n`. -/
@[stacks 08J5]
theorem mem_concentrated_iff (n : ℤ) (X : DerivedCategory 𝒜) :
    concentrated 𝒜 n X ↔ X.IsLE n ∧ X.IsGE n := sorry

/-- The ambient `singleFunctor` has essential image precisely the objects
concentrated in its degree. -/
@[stacks 08J5]
theorem singleFunctor_essImage (n : ℤ) :
    (DerivedCategory.singleFunctor 𝒜 n).essImage = concentrated 𝒜 n := sorry

namespace Concentrated

/-- The inclusion of degree-`n` concentrated objects into the derived category. -/
@[stacks 08J5]
noncomputable abbrev ι (n : ℤ) :
    Concentrated 𝒜 n ⥤ DerivedCategory 𝒜 :=
  (concentrated 𝒜 n).ι

/-- A bundled concentrated object satisfies its defining upper bound. -/
instance isLE (n : ℤ) (X : Concentrated 𝒜 n) : X.obj.IsLE n :=
  ⟨X.property.1⟩

/-- A bundled concentrated object satisfies its defining lower bound. -/
instance isGE (n : ℤ) (X : Concentrated 𝒜 n) : X.obj.IsGE n :=
  ⟨X.property.2⟩

/-- Bundle a raw derived object equipped with both degree-`n` bounds. -/
def ofBounds (X : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    Concentrated 𝒜 n :=
  ⟨X, ⟨Triangulated.TStructure.IsLE.le, Triangulated.TStructure.IsGE.ge⟩⟩

/-- Degree-`n` homology restricted to the full subcategory of objects
concentrated in degree `n`. -/
@[stacks 08J5]
noncomputable def homologyFunctor (n : ℤ) : Concentrated 𝒜 n ⥤ 𝒜 :=
  ι 𝒜 n ⋙ DerivedCategory.homologyFunctor 𝒜 n

/-- Restricted homology evaluates on the underlying derived object. -/
@[simp, stacks 08J5]
theorem homologyFunctor_obj (n : ℤ) (X : Concentrated 𝒜 n) :
    (homologyFunctor 𝒜 n).obj X =
      (DerivedCategory.homologyFunctor 𝒜 n).obj X.obj := sorry

/-- Restricted homology maps the underlying morphism in the derived category. -/
@[simp, stacks 08J5]
theorem homologyFunctor_map (n : ℤ) {X Y : Concentrated 𝒜 n} (f : X ⟶ Y) :
    (homologyFunctor 𝒜 n).map f =
      (DerivedCategory.homologyFunctor 𝒜 n).map f.hom := sorry

/-- The equivalence from the abelian category to the degree-`n` concentrated
subcategory induced by the essential image of `singleFunctor`. -/
@[stacks 08J5]
noncomputable def singleEquivalence (n : ℤ) : 𝒜 ≌ Concentrated 𝒜 n :=
  ((DerivedCategory.singleFunctor 𝒜 n).toEssImage).asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr (singleFunctor_essImage 𝒜 n))

/-- The lift of the ambient `singleFunctor` to the concentrated full
subcategory. -/
@[stacks 08J5]
noncomputable def singleFunctor (n : ℤ) : 𝒜 ⥤ Concentrated 𝒜 n :=
  (singleEquivalence 𝒜 n).functor

/-- After inclusion into the derived category, the lifted `singleFunctor`
agrees naturally with Mathlib's ambient `singleFunctor`. -/
@[stacks 08J5]
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor 𝒜 n ⋙ ι 𝒜 n ≅ DerivedCategory.singleFunctor 𝒜 n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor 𝒜 n).toEssImage
      (ObjectProperty.ιOfLECompιIso (singleFunctor_essImage 𝒜 n).le) ≪≫
    Functor.toEssImageCompι (DerivedCategory.singleFunctor 𝒜 n)

/-- The ambient inclusion factors through the inverse of the single-object
equivalence followed by the ambient `singleFunctor`. -/
noncomputable def inclusionIsoInverse (n : ℤ) :
    ι 𝒜 n ≅
      (singleEquivalence 𝒜 n).inverse ⋙ DerivedCategory.singleFunctor 𝒜 n :=
  (ι 𝒜 n).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (singleEquivalence 𝒜 n).counitIso.symm (ι 𝒜 n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (singleEquivalence 𝒜 n).inverse (singleFunctorCompιIso 𝒜 n)

/-- Restricted degree-`n` homology is naturally isomorphic to the inverse of
the single-object equivalence. -/
@[stacks 08J5]
noncomputable def homologyIsoInverse (n : ℤ) :
    homologyFunctor 𝒜 n ≅ (singleEquivalence 𝒜 n).inverse :=
  Functor.isoWhiskerRight (inclusionIsoInverse 𝒜 n)
      (DerivedCategory.homologyFunctor 𝒜 n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (singleEquivalence 𝒜 n).inverse
      (DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒜 n) ≪≫
    (singleEquivalence 𝒜 n).inverse.rightUnitor

/-- Restricted degree-`n` homology is the inverse equivalence from concentrated
objects to the abelian category. -/
@[stacks 08J5]
noncomputable def homologyEquivalence (n : ℤ) : Concentrated 𝒜 n ≌ 𝒜 :=
  (singleEquivalence 𝒜 n).symm.changeFunctor (homologyIsoInverse 𝒜 n).symm

/-- The forward functor of `homologyEquivalence` is restricted degree-`n`
homology. -/
@[simp, stacks 08J5]
theorem homologyEquivalence_functor (n : ℤ) :
    (homologyEquivalence 𝒜 n).functor = homologyFunctor 𝒜 n := sorry

/-- Restricted degree-`n` homology is canonically an equivalence of categories. -/
@[stacks 08J5]
noncomputable instance homologyFunctorIsEquivalence (n : ℤ) :
    (homologyFunctor 𝒜 n).IsEquivalence :=
  (homologyEquivalence 𝒜 n).isEquivalence_functor

/-- A concentrated object is identified with the single object on its own
degree-`n` homology by the equivalence counit. -/
@[stacks 08J5]
noncomputable def objIso (n : ℤ) (X : Concentrated 𝒜 n) :
    X.obj ≅ (DerivedCategory.singleFunctor 𝒜 n).obj
      ((homologyFunctor 𝒜 n).obj X) :=
  (ι 𝒜 n).mapIso ((singleEquivalence 𝒜 n).counitIso.symm.app X) ≪≫
    (singleFunctorCompιIso 𝒜 n).app ((singleEquivalence 𝒜 n).inverse.obj X) ≪≫
    (DerivedCategory.singleFunctor 𝒜 n).mapIso
      ((homologyIsoInverse 𝒜 n).symm.app X)

/-- The objectwise concentrated-to-single isomorphisms are natural. -/
@[stacks 08J5]
theorem objIso_naturality (n : ℤ) {X Y : Concentrated 𝒜 n} (f : X ⟶ Y) :
    (ι 𝒜 n).map f ≫ (objIso 𝒜 n Y).hom =
      (objIso 𝒜 n X).hom ≫
        (DerivedCategory.singleFunctor 𝒜 n).map ((homologyFunctor 𝒜 n).map f) := sorry

/-- The inclusion of concentrated objects is naturally the single-object
realization of their degree-`n` homology. -/
@[stacks 08J5]
noncomputable def inclusionIso (n : ℤ) :
    ι 𝒜 n ≅ homologyFunctor 𝒜 n ⋙ DerivedCategory.singleFunctor 𝒜 n :=
  NatIso.ofComponents (objIso 𝒜 n) (objIso_naturality 𝒜 n)

/-- The component of `inclusionIso` is `objIso`. -/
@[simp, stacks 08J5]
theorem inclusionIso_app (n : ℤ) (X : Concentrated 𝒜 n) :
    (inclusionIso 𝒜 n).app X = objIso 𝒜 n X := sorry

/-- On degree-`n` homology, the forward map of `objIso` is normalized by
`singleFunctorCompHomologyFunctorIso` to the identity. -/
@[reassoc (attr := simp), stacks 08J5]
theorem objIso_homology_hom (n : ℤ) (X : Concentrated 𝒜 n) :
    (DerivedCategory.homologyFunctor 𝒜 n).map (objIso 𝒜 n X).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒜 n).hom.app
          ((homologyFunctor 𝒜 n).obj X) =
      𝟙 ((homologyFunctor 𝒜 n).obj X) := sorry

/-- Raw-object compatibility form of `objIso` for callers that already have
the two concentration bounds as typeclass facts. -/
@[stacks 08J5]
noncomputable def singleIsoOfBounds (X : DerivedCategory 𝒜) (n : ℤ)
    [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor 𝒜 n).obj
      ((DerivedCategory.homologyFunctor 𝒜 n).obj X) :=
  objIso 𝒜 n (ofBounds 𝒜 X n)

end Concentrated

end CategoryTheory.DerivedCategory

end
