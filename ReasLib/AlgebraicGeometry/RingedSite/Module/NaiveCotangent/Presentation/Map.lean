/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationBaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of presentationwise naive cotangent complexes

A morphism between two composable presentations is a morphism of the three ring-sheaf terms.
This file first constructs the induced map on conormal modules sectionwise, then descends it
through module sheafification and extension of scalars.  This is the reusable data layer needed
for maps of presentationwise naive cotangent complexes.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.NaiveCotangent.Presentation

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable {A P B A' P' B' : Sheaf J CommRingCat.{w}}
variable {phi : A ⟶ P} {alpha : P ⟶ B}
variable {phi' : A' ⟶ P'} {alpha' : P' ⟶ B'}

/-- A morphism between two composable presentations `A ⟶ P ⟶ B` and
`A' ⟶ P' ⟶ B'`. -/
@[ext, stacks 08TY "morphism of presentations"]
structure Hom (phi : A ⟶ P) (alpha : P ⟶ B)
    (phi' : A' ⟶ P') (alpha' : P' ⟶ B') where
  /-- The morphism between the base ring sheaves. -/
  base : A ⟶ A'
  /-- The morphism between the presenting ring sheaves. -/
  middle : P ⟶ P'
  /-- The morphism between the presented ring sheaves. -/
  target : B ⟶ B'
  /-- The square formed by the base and presenting ring sheaves commutes. -/
  baseSq : CommSq base phi phi' middle
  /-- The square formed by the presenting and presented ring sheaves commutes. -/
  targetSq : CommSq middle alpha alpha' target

namespace Hom

/-- The upper square of the identity morphism of a presentation commutes. -/
theorem id_baseSq (phi : A ⟶ P) :
    CommSq (𝟙 A) phi phi (𝟙 P) := sorry

/-- The lower square of the identity morphism of a presentation commutes. -/
theorem id_targetSq (alpha : P ⟶ B) :
    CommSq (𝟙 P) alpha alpha (𝟙 B) := sorry

/-- The identity morphism of a composable presentation. -/
def id (phi : A ⟶ P) (alpha : P ⟶ B) :
    Hom phi alpha phi alpha where
  base := 𝟙 A
  middle := 𝟙 P
  target := 𝟙 B
  baseSq := id_baseSq phi
  targetSq := id_targetSq alpha

/-- The upper square of a composite of morphisms of presentations commutes. -/
theorem comp_baseSq
    {A'' P'' B'' : Sheaf J CommRingCat.{w}}
    {phi'' : A'' ⟶ P''} {alpha'' : P'' ⟶ B''}
    (f : Hom phi alpha phi' alpha')
    (g : Hom phi' alpha' phi'' alpha'') :
    CommSq (f.base ≫ g.base) phi phi'' (f.middle ≫ g.middle) := sorry

/-- The lower square of a composite of morphisms of presentations commutes. -/
theorem comp_targetSq
    {A'' P'' B'' : Sheaf J CommRingCat.{w}}
    {phi'' : A'' ⟶ P''} {alpha'' : P'' ⟶ B''}
    (f : Hom phi alpha phi' alpha')
    (g : Hom phi' alpha' phi'' alpha'') :
    CommSq (f.middle ≫ g.middle) alpha alpha'' (f.target ≫ g.target) := sorry

/-- Composition of morphisms of composable presentations. -/
def comp
    {A'' P'' B'' : Sheaf J CommRingCat.{w}}
    {phi'' : A'' ⟶ P''} {alpha'' : P'' ⟶ B''}
    (f : Hom phi alpha phi' alpha')
    (g : Hom phi' alpha' phi'' alpha'') :
    Hom phi alpha phi'' alpha'' where
  base := f.base ≫ g.base
  middle := f.middle ≫ g.middle
  target := f.target ≫ g.target
  baseSq := comp_baseSq f g
  targetSq := comp_targetSq f g

/-- The two commutativity relations defining a morphism of composable presentations. -/
theorem commutes (f : Hom phi alpha phi' alpha') :
    f.base ≫ phi' = phi ≫ f.middle ∧
      f.middle ≫ alpha' = alpha ≫ f.target := sorry

/-- Right composition with the identity morphism of a presentation is trivial. -/
theorem comp_id (f : Hom phi alpha phi' alpha') :
    f.comp (id phi' alpha') = f := sorry

/-- Left composition with the identity morphism of a presentation is trivial. -/
theorem id_comp (f : Hom phi alpha phi' alpha') :
    (id phi alpha).comp f = f := sorry

namespace Conormal

/-- A morphism of presentations sends the source kernel ideal into the target kernel ideal on
every object of the site. -/
theorem ideal_le_comap
    (f : Hom phi alpha phi' alpha') (U : Cᵒᵖ) :
    conormalIdeal alpha U ≤
      (conormalIdeal alpha' U).comap ((f.middle.hom.app U).hom) := sorry

/-- The sectionwise map `Ker(alpha) / Ker(alpha)^2 ⟶ Ker(alpha') / Ker(alpha')^2` induced by a
morphism of presentations.  Its codomain is restricted along the middle ring map. -/
noncomputable abbrev app
    (f : Hom phi alpha phi' alpha') (U : Cᵒᵖ) :
    conormalObj alpha U ⟶
      (ModuleCat.restrictScalars ((f.middle.hom.app U).hom)).obj
        (conormalObj alpha' U) :=
  ConcreteCategory.ofHom (C := ModuleCat (P.obj.obj U))
    (@Ideal.mapCotangent
      (P.obj.obj U) _ (P.obj.obj U) (P'.obj.obj U) _ _
      (Algebra.id (P.obj.obj U)) ((f.middle.hom.app U).hom.toAlgebra)
      (conormalIdeal alpha U) (conormalIdeal alpha' U)
      (@Algebra.ofId (P.obj.obj U) (P'.obj.obj U) _ _
        ((f.middle.hom.app U).hom.toAlgebra))
      (ideal_le_comap f U))

/-- On cotangent generators, the sectionwise conormal map applies the middle ring map to a
representative of the kernel ideal. -/
theorem app_toCotangent
    (f : Hom phi alpha phi' alpha') (U : Cᵒᵖ)
    (x : conormalIdeal alpha U) :
    app f U ((conormalIdeal alpha U).toCotangent x) =
      (conormalIdeal alpha' U).toCotangent
        ⟨(f.middle.hom.app U).hom x, ideal_le_comap f U x.2⟩ := sorry


/-- The sectionwise conormal maps commute with restriction in the site. -/
theorem app_naturality
    (f : Hom phi alpha phi' alpha') {U V : Cᵒᵖ} (i : U ⟶ V) :
    (conormalPresheaf alpha).map i ≫
        (ModuleCat.restrictScalars (((ringSheaf J P).obj.map i).hom)).map
          (app f V) =
      app f U ≫
        ((PresheafOfModules.restrictScalars (ringSheafMap f.middle).hom).obj
          (conormalPresheaf alpha')).map i := sorry

/-- The morphism of conormal presheaves induced by a morphism of presentations. -/
@[stacks 08TY "conormal presheaf map"]
noncomputable def presheafMap
    (f : Hom phi alpha phi' alpha') :
    conormalPresheaf alpha ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap f.middle).hom).obj
        (conormalPresheaf alpha') where
  app U := app f U
  naturality i := app_naturality f i


/-- The sheafified conormal map, still viewed over the source presenting ring sheaf. -/
@[stacks 08TY "conormal sheaf map"]
noncomputable def overMiddle
    (f : Hom phi alpha phi' alpha') :
    conormalSourceOverSource alpha ⟶
      (restrictionAlong f.middle).obj (conormalSourceOverSource alpha') :=
  ModuleSheafification.mapToRestriction f.middle (presheafMap f)

end Conormal


/-- The lower square of a morphism of presentations remains commutative after forgetting
commutativity. -/
theorem targetSq_forget
    (f : Hom phi alpha phi' alpha') :
    ringSheafMap (alpha ≫ f.target) =
      ringSheafMap f.middle ≫ ringSheafMap alpha' := sorry

/-- The two ways of restricting a module from the target presented ring to the source
presenting ring are canonically isomorphic. -/
noncomputable def restrictionIso
    (f : Hom phi alpha phi' alpha') :
    restrictionAlong alpha' ⋙ restrictionAlong f.middle ≅
      restrictionAlong f.target ⋙ restrictionAlong alpha :=
  (SheafOfModules.Restriction.compIso'
      (ringSheafMap f.middle) (ringSheafMap alpha')
      (ringSheafMap (alpha ≫ f.target)) (targetSq_forget f)).trans
    (SheafOfModules.Restriction.compIso'
      (ringSheafMap alpha) (ringSheafMap f.target)
      (ringSheafMap (alpha ≫ f.target))
      (SheafOfModules.RingedSite.ringSheafMap_comp alpha f.target)).symm

/-- Extend a map over the middle ring sheaves to a map over the presented target ring sheaves.
The construction uses only the two extension-restriction adjunctions and restriction coherence. -/
@[stacks 08TY "extension of a presentation map"]
noncomputable def extend
    (f : Hom phi alpha phi' alpha')
    {M : SheafOfModules (ringSheaf J P)}
    {M' : SheafOfModules (ringSheaf J P')}
    (g : M ⟶ (restrictionAlong f.middle).obj M') :
    (extendAlong f.target).obj ((extendAlong alpha).obj M) ⟶
      (extendAlong alpha').obj M' :=
  ((extendRestrictAdj f.target).homEquiv _ _).symm
    (((extendRestrictAdj alpha).homEquiv _ _).symm
      (g ≫
        (restrictionAlong f.middle).map
          ((extendRestrictAdj alpha').unit.app M') ≫
        (restrictionIso f).hom.app ((extendAlong alpha').obj M')))

namespace Conormal

/-- The map on degree `-1` conormal terms induced by a morphism of presentations. -/
@[stacks 08TY "conormal term map"]
noncomputable def map
    (f : Hom phi alpha phi' alpha') :
    (extendAlong f.target).obj (conormalSource alpha) ⟶
      conormalSource alpha' :=
  extend f (overMiddle f)

end Conormal

namespace Differentials

/-- The map on degree `0` differential terms induced by a morphism of presentations. -/
@[stacks 08TY "differential term map"]
noncomputable def map
    (f : Hom phi alpha phi' alpha') :
    (extendAlong f.target).obj (conormalTensorTerm phi alpha) ⟶
      conormalTensorTerm phi' alpha' :=
  extend f (RelativeDifferentials.map f.baseSq)

end Differentials

/-- The component function underlying the map of presentationwise naive cotangent complexes. -/
noncomputable def component
    (f : Hom phi alpha phi' alpha') (n : ℤ) :
    (extendAlong f.target).obj (term phi alpha n) ⟶ term phi' alpha' n :=
  match n with
  | Int.negSucc 0 => Conormal.map f
  | Int.ofNat 0 => Differentials.map f
  | _ => 0

/-- The component maps commute with the differentials of the presentationwise naive cotangent
complexes. -/
theorem component_comm
    (f : Hom phi alpha phi' alpha') (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    component f i ≫ (complex phi' alpha').d i j =
      ((extendComplex f.target).obj (complex phi alpha)).d i j ≫
        component f j := sorry

/-- The cochain map induced by a morphism of presentations. -/
@[stacks 08TY "map of presentationwise naive cotangent complexes"]
noncomputable def map
    (f : Hom phi alpha phi' alpha') :
    (extendComplex f.target).obj (complex phi alpha) ⟶ complex phi' alpha' where
  f n := component f n
  comm' i j hij := component_comm f i j hij

/-- The degree `-1` component of the presentation map is the conormal-term map. -/
theorem map_f_negOne (f : Hom phi alpha phi' alpha') :
    (map f).f (-1) = Conormal.map f := sorry

/-- The degree `0` component of the presentation map is the tensor-differential map. -/
theorem map_f_zero (f : Hom phi alpha phi' alpha') :
    (map f).f 0 = Differentials.map f := sorry

/-- The cochain map induced by the identity morphism of a presentation is the canonical
identity-extension comparison. -/
theorem map_id (phi : A ⟶ P) (alpha : P ⟶ B) :
    map (id phi alpha) =
      (extendComplexIdIso B).hom.app (complex phi alpha) := sorry

/-- Cochain maps induced by morphisms of presentations respect composition, with the canonical
comparison between successive extension of scalars and extension along the composite. -/
theorem map_comp
    {A'' P'' B'' : Sheaf J CommRingCat.{w}}
    {phi'' : A'' ⟶ P''} {alpha'' : P'' ⟶ B''}
    (f : Hom phi alpha phi' alpha')
    (g : Hom phi' alpha' phi'' alpha'') :
    map (comp f g) =
      (extendComplexCompIso f.target g.target).inv.app
          (complex phi alpha) ≫
        (extendComplex g.target).map (map f) ≫ map g := sorry

end Hom

end SheafOfModules.RingedSite.NaiveCotangent.Presentation
