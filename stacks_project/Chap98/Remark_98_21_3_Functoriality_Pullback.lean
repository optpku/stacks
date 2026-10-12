/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import stacks_project.Chap98.Lemma_98_21_1
public import stacks_project.Chap98.Lemma_98_21_2_Functor

/-!
# Pullback of lifts along a change of rings

An `S`-algebra map `A ⟶ B` and an `A`-linear map `M ⟶ N` induce a ring map
`A[M] ⟶ B[N]`, hence an identity-1-morphism pullback of lift categories. The
same construction applies to a commutative square of first-order thickenings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.Deformation
open FiberedCategoryOver.Groupoids (fiberFunctor)
open TrivSqZeroExt
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The ring map `A[M] ⟶ B[N]` induced by `v : A ⟶ B` and an `A`-linear map
`M ⟶ N`. -/
def trivSqZeroMapRestrict {A B : CommRingCat.{u}} (v : A ⟶ B)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N) :
    trivSqZero A M ⟶ trivSqZero B N :=
  CommRingCat.ofHom
    { toFun x := (v.hom x.fst, f x.snd)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Evaluating `trivSqZeroMapRestrict` on an element of `A[M]` sends the pair of
projections to `(v.hom fst, f snd)`. -/
theorem trivSqZeroMapRestrict_apply {A B : CommRingCat.{u}} (v : A ⟶ B)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : trivSqZero A M) :
    (trivSqZeroMapRestrict v f).hom x = (v.hom x.fst, f x.snd) := sorry

/-- The square `A[M] ⟶ A ⟶ B` equals `A[M] ⟶ B[N] ⟶ B`. -/
theorem trivSqZeroMapRestrict_comp_fst {A B : CommRingCat.{u}} (v : A ⟶ B)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N) :
    trivSqZeroHom A M ≫ v = trivSqZeroMapRestrict v f ≫ trivSqZeroHom B N := sorry

/-- `Spec` of `A[M] ⟶ B[N]` is compatible with the structure morphisms of
`Spec(A[M])` and `Spec(B[N])`. -/
theorem trivSqZeroMapRestrict_spec {S : Scheme.{u}} {A B : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N) :
    Spec.map (trivSqZeroMapRestrict v f) ≫ specTrivSqZero σA M = specTrivSqZero σB N :=
  sorry

/-- The morphism in `Over S` associated with `A[M] ⟶ B[N]`. -/
def specOverMapRestrict {S : Scheme.{u}} {A B : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N) :
    Over.mk (specTrivSqZero σB N) ⟶ Over.mk (specTrivSqZero σA M) :=
  specOverHom (trivSqZeroMapRestrict v f) (trivSqZeroMapRestrict_spec v hv f)

/-- Reindexing along `specOverMapRestrict` after `specOverInl` on `A[M]` recovers
the composite through `Spec(B)`. -/
theorem specOverMapRestrict_comp_inl {S : Scheme.{u}} {A B : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N) :
    specOverMapRestrict v hv f ≫ specOverInl σA M =
      specOverInl σB N ≫ specOverHom v hv := sorry

/-- The image of a kernel element under a commuting square of square-zero
thickenings remains in the kernel. -/
theorem kernelHom_mem {A A' B B' : CommRingCat.{u}}
    (fA : A' ⟶ A) (fB : B' ⟶ B)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (u : A' ⟶ B') (sq : CommSq fA u v fB)
    (x : kernelObj fA) :
    u.hom x.1 ∈ RingHom.ker fB.hom := sorry

/-- The `A`-linear map `Ker(A' ⟶ A) ⟶ Ker(B' ⟶ B)` induced by a commuting square
of square-zero thickenings. -/
def kernelHom {A A' B B' : CommRingCat.{u}}
    (fA : A' ⟶ A) (fB : B' ⟶ B)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (u : A' ⟶ B') (sq : CommSq fA u v fB) :
    kernelObj fA ⟶ (ModuleCat.restrictScalars v.hom).obj (kernelObj fB) :=
  ConcreteCategory.ofHom
    { toFun x := ⟨u.hom x.1, kernelHom_mem fA fB v u sq x⟩
      map_add' := sorry
      map_smul' := sorry }

/-- `kernelHom` evaluates the source ring map on a kernel element. -/
theorem kernelHom_apply {A A' B B' : CommRingCat.{u}}
    (fA : A' ⟶ A) (fB : B' ⟶ B)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (u : A' ⟶ B') (sq : CommSq fA u v fB)
    (x : kernelObj fA) :
    kernelHom fA fB v u sq x = ⟨u.hom x.1, kernelHom_mem fA fB v u sq x⟩ := sorry

/-- Identity-cleavage comparison so a fibre morphism
`φ : x|_Spec(B) ⟶ y` feeds `liftFunctor (𝟙 X)`. -/
def idReindexConnect {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    Chosen.reindexObj X.p (specOverHom v hv)
      ((fiberFunctor (𝟙 X) (Over.mk σA)).obj x) ⟶ y :=
  eqToHom
    (congrArg (fun F ↦ Chosen.reindexObj X.p (specOverHom v hv) (F.obj x))
      (fiberFunctor.id X (Over.mk σA))) ≫ φ

/-- The identity-1-morphism pullback `Lift(x, A') ⥤ Lift(y, B')` of a commutative
square of `S`-algebra thickenings and a fibre morphism `φ : x|_Spec(B) ⟶ y`.
The identity `φ` recovers the restriction `y = x|_Spec(B)`. In Stacks language a
morphism of deformation situations is written
`(y, B' ⟶ B) ⟶ (x, A' ⟶ A)`, opposite to this covariant square. -/
def liftPullback {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    liftCat x fA hfA ⥤ liftCat y fB hfB :=
  liftFunctor (𝟙 X) fA hfA fB hfB v hv u hu sq x y (idReindexConnect v hv x y φ)

/-- The object function of `liftPullback` is that of `liftFunctor (𝟙 X)`. -/
theorem liftPullback_obj {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (a : liftCat x fA hfA) :
    (liftPullback fA hfA fB hfB v hv u hu sq x y φ).obj a =
      (liftFunctor (𝟙 X) fA hfA fB hfB v hv u hu sq x y
        (idReindexConnect v hv x y φ)).obj a := sorry

/-- The morphism function of `liftPullback` is that of `liftFunctor (𝟙 X)`. -/
theorem liftPullback_map {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    {a b : liftCat x fA hfA} (η : a ⟶ b) :
    (liftPullback fA hfA fB hfB v hv u hu sq x y φ).map η =
      (liftFunctor (𝟙 X) fA hfA fB hfB v hv u hu sq x y
        (idReindexConnect v hv x y φ)).map η := sorry

/-- The pullback functor `Lift(x, A[M]) ⥤ Lift(y, B[N])` induced by `A ⟶ B` and
an `A`-linear map `M ⟶ N`. -/
def trivSqZeroLiftPullback {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) ⥤
      liftCat y (trivSqZeroHom B N) (trivSqZeroHom_comp σB N) :=
  liftPullback (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)
    (trivSqZeroHom B N) (trivSqZeroHom_comp σB N)
    v hv (trivSqZeroMapRestrict v f) (trivSqZeroMapRestrict_spec v hv f)
    ⟨trivSqZeroMapRestrict_comp_fst v f⟩ x y φ

/-- Well-definedness of isomorphism-class pullback along a functor of lift
categories. -/
theorem liftsMap_wd {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {y : X.p.Fiber (Over.mk σB)}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    {fB : B' ⟶ B} {hfB : Spec.map fB ≫ σB' = σB}
    (F : liftCat x fA hfA ⥤ liftCat y fB hfB)
    {a b : liftCat x fA hfA} (h : Nonempty (a ≅ b)) :
    lifts.mk (F.obj a) = lifts.mk (F.obj b) := sorry

/-- The map `Lift(x, A') → Lift(y, B')` of isomorphism classes induced by a
functor of lift categories. -/
def liftsMap {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {y : X.p.Fiber (Over.mk σB)}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    {fB : B' ⟶ B} {hfB : Spec.map fB ≫ σB' = σB}
    (F : liftCat x fA hfA ⥤ liftCat y fB hfB) :
    lifts x fA hfA → lifts y fB hfB :=
  Quotient.lift (fun a ↦ lifts.mk (F.obj a)) (fun _ _ h ↦ liftsMap_wd F h)

/-- `liftsMap` sends the class of a lift to the class of its image. -/
theorem liftsMap_mk {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {y : X.p.Fiber (Over.mk σB)}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    {fB : B' ⟶ B} {hfB : Spec.map fB ≫ σB' = σB}
    (F : liftCat x fA hfA ⥤ liftCat y fB hfB) (a : liftCat x fA hfA) :
    liftsMap F (lifts.mk a) = lifts.mk (F.obj a) := sorry

/-- The selected fibre object of the trivial deformation lift is the trivial
deformation. -/
def trivialDeformationLift_codomainIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (trivialDeformationLift x M).codomain ≅ trivialDeformation x M :=
  Fiber.isoMk (Iso.refl _)
    (IsHomLift.id (trivialDeformationLift x M).codomain.2)

/-- The comparison identifying successive reindexing of `x` along `inl_A` and
`A[M] ⟶ B[N]` with reindexing along the composite through `Spec(B)`. -/
def trivialDeformationRestrictCompIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) :
    Chosen.reindexObj X.p (specOverInl σB N ≫ specOverHom v hv) x ≅
      Chosen.reindexObj X.p (specOverMapRestrict v hv f) (trivialDeformation x M) :=
  Chosen.Reindex.specifiedCompIsoApp X.p (specOverInl σA M)
    (specOverMapRestrict v hv f) (specOverInl σB N ≫ specOverHom v hv)
    (specOverMapRestrict_comp_inl v hv f) x

/-- The comparison identifying successive reindexing of `x` along `Spec(B)` and
`inl_B` with reindexing along the same composite. -/
def trivialDeformationSectionCompIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (N : ModuleCat.{u} B) (x : X.p.Fiber (Over.mk σA)) :
    Chosen.reindexObj X.p (specOverInl σB N ≫ specOverHom v hv) x ≅
      Chosen.reindexObj X.p (specOverInl σB N)
        (Chosen.reindexObj X.p (specOverHom v hv) x) :=
  Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v hv)
    (specOverInl σB N) (specOverInl σB N ≫ specOverHom v hv) rfl x

/-- Fibre isomorphism `y|_Spec(B[N]) ≅ (x|_Spec(A[M]))|_Spec(B[N])` induced by
`φ : x|_Spec(B) ⟶ y`. -/
def trivialDeformationReindexIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (N : ModuleCat.{u} B)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    Chosen.reindexObj X.p (specOverInl σB N)
      (Chosen.reindexObj X.p (specOverHom v hv) x) ≅ trivialDeformation y N where
  hom := Chosen.reindexMap X.p (specOverInl σB N) φ
  inv := Chosen.reindexMap X.p (specOverInl σB N) (inv φ)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Fibre isomorphism identifying the restriction of the trivial deformation of
`x` along `A[M] ⟶ B[N]` with the trivial deformation of `y`. -/
def trivialDeformationRestrictIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    Chosen.reindexObj X.p (specOverMapRestrict v hv f) (trivialDeformation x M) ≅
      trivialDeformation y N :=
  (trivialDeformationRestrictCompIso v hv f x).symm ≪≫
    trivialDeformationSectionCompIso v hv N x ≪≫
    trivialDeformationReindexIso v hv N x y φ

/-- Identity-cleavage comparison on the selected reindexing of the trivial
deformation lift along `A[M] ⟶ B[N]`. -/
def trivSqZeroLiftPullback_idReindex {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) :
    Chosen.reindexObj X.p (specOverMapRestrict v hv f)
      ((fiberFunctor (𝟙 X) (Over.mk (specTrivSqZero σA M))).obj
        (trivialDeformationLift x M).codomain) ≅
      Chosen.reindexObj X.p (specOverMapRestrict v hv f)
        (trivialDeformationLift x M).codomain :=
  eqToIso
    (congrArg
      (fun F ↦ Chosen.reindexObj X.p (specOverMapRestrict v hv f)
        (F.obj (trivialDeformationLift x M).codomain))
      (fiberFunctor.id X (Over.mk (specTrivSqZero σA M))))

/-- The pullback of the trivial deformation lift has fibre-codomain the selected
reindexing of that lift along `A[M] ⟶ B[N]`. -/
def trivSqZeroLiftPullback_codomainIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    ((trivSqZeroLiftPullback v hv f x y φ).obj (trivialDeformationLift x M)).codomain ≅
      Chosen.reindexObj X.p (specOverMapRestrict v hv f)
        ((fiberFunctor (𝟙 X) (Over.mk (specTrivSqZero σA M))).obj
          (trivialDeformationLift x M).codomain) :=
  Fiber.isoMk (Iso.refl _)
    (IsHomLift.id
      ((trivSqZeroLiftPullback v hv f x y φ).obj
        (trivialDeformationLift x M)).codomain.2)

/-- Fibre comparison from the pullback of the trivial deformation lift to the
trivial deformation of `y`. -/
def trivialDeformationPullback_codomainIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    ((trivSqZeroLiftPullback v hv f x y φ).obj (trivialDeformationLift x M)).codomain ≅
      (trivialDeformationLift y N).codomain :=
  trivSqZeroLiftPullback_codomainIso v hv f x y φ ≪≫
    trivSqZeroLiftPullback_idReindex v hv f x ≪≫
    (Chosen.reindex X.p (specOverMapRestrict v hv f)).mapIso
      (trivialDeformationLift_codomainIso x M) ≪≫
    trivialDeformationRestrictIso v hv f x y φ ≪≫
    (trivialDeformationLift_codomainIso y N).symm

/-- The cartesian comparison in the lift category identifying the pullback of
the trivial deformation of `x` with the trivial deformation of `y`. -/
def trivialDeformationPullback {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    (trivSqZeroLiftPullback v hv f x y φ).obj (trivialDeformationLift x M) ≅
      trivialDeformationLift y N where
  hom := UnderLift.homMk (trivialDeformationPullback_codomainIso v hv f x y φ).hom sorry
  inv := UnderLift.homMk (trivialDeformationPullback_codomainIso v hv f x y φ).inv sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Convert an infinitesimal automorphism of a lift to a lift-category
automorphism. -/
def liftAutOfInfinitesimal {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
    {hfA : Spec.map fA ≫ σA' = σA}
    (x' : liftCat x fA hfA) (α : infinitesimalAut x') : Aut x' where
  hom := UnderLift.homMk α.val.hom sorry
  inv := UnderLift.homMk α.val.inv sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Convert a lift-category automorphism to an infinitesimal automorphism of the
lift. -/
def infinitesimalAutOfLiftAut {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
    {hfA : Spec.map fA ≫ σA' = σA}
    (x' : liftCat x fA hfA) (η : Aut x') : infinitesimalAut x' :=
  ⟨{ hom := η.hom.val
     inv := η.inv.val
     hom_inv_id := sorry
     inv_hom_id := sorry }, sorry⟩

/-- Restriction `Inf(x'/x) ⟶ Inf(F(x')/y)` along a functor of lift categories,
as an `A`-linear map into the restriction of scalars of the `B`-module
`Inf(F(x')/y)`. -/
def infinitesimalAutRestrict {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {y : X.p.Fiber (Over.mk σB)}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    {fB : B' ⟶ B} {hfB : Spec.map fB ≫ σB' = σB}
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B)
    (F : liftCat x fA hfA ⥤ liftCat y fB hfB)
    (x' : liftCat x fA hfA) :
    ModuleCat.of A (infinitesimalAut x') ⟶
      (ModuleCat.restrictScalars v.hom).obj
        (ModuleCat.of B (infinitesimalAut (F.obj x'))) :=
  ConcreteCategory.ofHom
    { toFun α := infinitesimalAutOfLiftAut (F.obj x')
        (F.mapIso (liftAutOfInfinitesimal x' α))
      map_add' := sorry
      map_smul' := sorry }

/-- Evaluating `infinitesimalAutRestrict` applies the functor of lift categories
to the corresponding automorphism. -/
theorem infinitesimalAutRestrict_apply {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {y : X.p.Fiber (Over.mk σB)}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    {fB : B' ⟶ B} {hfB : Spec.map fB ≫ σB' = σB}
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B)
    (F : liftCat x fA hfA ⥤ liftCat y fB hfB)
    (x' : liftCat x fA hfA) (α : infinitesimalAut x') :
    infinitesimalAutRestrict v F x' α =
      infinitesimalAutOfLiftAut (F.obj x')
        (F.mapIso (liftAutOfInfinitesimal x' α)) := sorry

end AlgebraicGeometry.GroupoidsOver
