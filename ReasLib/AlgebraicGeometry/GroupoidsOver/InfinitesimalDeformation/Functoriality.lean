module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation

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
  let g : trivSqZero A M → trivSqZero B N := fun x ↦ (v.hom x.fst, f x.snd)
  have laws : g 1 = 1 ∧ (∀ a b, g (a * b) = g a * g b) ∧
      g 0 = 0 ∧ (∀ a b, g (a + b) = g a + g b) := by
    sorry
  CommRingCat.ofHom
    { toFun := g
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2 }

/-- Evaluating `trivSqZeroMapRestrict` on an element of `A[M]` sends the pair of
projections to `(v.hom fst, f snd)`. -/
theorem trivSqZeroMapRestrict_apply {A B : CommRingCat.{u}} (v : A ⟶ B)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : trivSqZero A M) :
    (trivSqZeroMapRestrict v f).hom x = (v.hom x.fst, f x.snd) := by rfl

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
  let g : kernelObj fA → (ModuleCat.restrictScalars v.hom).obj (kernelObj fB) :=
    fun x ↦ ⟨u.hom x.1, kernelHom_mem fA fB v u sq x⟩
  have laws : (∀ a b, g (a + b) = g a + g b) ∧
      (∀ (r : A) a, g (r • a) = r • g a) := by
    sorry
  ConcreteCategory.ofHom
    { toFun := g
      map_add' := laws.1
      map_smul' := laws.2 }

/-- `kernelHom` evaluates the source ring map on a kernel element. -/
theorem kernelHom_apply {A A' B B' : CommRingCat.{u}}
    (fA : A' ⟶ A) (fB : B' ⟶ B)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (u : A' ⟶ B') (sq : CommSq fA u v fB)
    (x : kernelObj fA) :
    kernelHom fA fB v u sq x = ⟨u.hom x.1, kernelHom_mem fA fB v u sq x⟩ := by rfl

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
  liftFunctor (𝟙 X) fA hfA fB hfB v hv u hu sq x y (eqToHom
    (congrArg (fun F ↦ Chosen.reindexObj X.p (specOverHom v hv) (F.obj x))
      (fiberFunctor.id X (Over.mk σA))) ≫ φ)

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
  Quotient.lift (fun a ↦ lifts.mk (F.obj a)) (by
    intro a b h
    exact (lifts.mk_eq_mk (F.obj a) (F.obj b)).2 (h.map F.mapIso))

/-- `liftsMap` sends the class of a lift to the class of its image. -/
theorem liftsMap_mk {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {y : X.p.Fiber (Over.mk σB)}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    {fB : B' ⟶ B} {hfB : Spec.map fB ≫ σB' = σB}
    (F : liftCat x fA hfA ⥤ liftCat y fB hfB) (a : liftCat x fA hfA) :
    liftsMap F (lifts.mk a) = lifts.mk (F.obj a) := by rfl

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
  (Chosen.Reindex.specifiedCompIsoApp X.p (specOverInl σA M)
    (specOverMapRestrict v hv f) (specOverInl σB N ≫ specOverHom v hv)
    (specOverMapRestrict_comp_inl v hv f) x).symm ≪≫
    Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v hv)
      (specOverInl σB N) (specOverInl σB N ≫ specOverHom v hv) rfl x ≪≫
    (Chosen.reindex X.p (specOverInl σB N)).mapIso (asIso φ)

/-- Convert an infinitesimal automorphism of a lift to a lift-category
automorphism. -/
def liftAutOfInfinitesimal {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
    {hfA : Spec.map fA ≫ σA' = σA}
    (x' : liftCat x fA hfA) (α : infinitesimalAut x') : Aut x' := by
  have laws : (x'.hom ≫ Fiber.fiberInclusion.map α.val.hom = x'.hom) ∧
      (x'.hom ≫ Fiber.fiberInclusion.map α.val.inv = x'.hom) ∧
      (α.val.hom ≫ α.val.inv = 𝟙 x'.codomain) ∧
      (α.val.inv ≫ α.val.hom = 𝟙 x'.codomain) := by
    sorry
  exact
    { hom := UnderLift.homMk α.val.hom laws.1
      inv := UnderLift.homMk α.val.inv laws.2.1
      hom_inv_id := Subtype.ext laws.2.2.1
      inv_hom_id := Subtype.ext laws.2.2.2 }

/-- Convert a lift-category automorphism to an infinitesimal automorphism of the
lift. -/
def infinitesimalAutOfLiftAut {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
    {hfA : Spec.map fA ≫ σA' = σA}
    (x' : liftCat x fA hfA) (η : Aut x') : infinitesimalAut x' :=
  have laws : (η.hom.val ≫ η.inv.val = 𝟙 x'.codomain) ∧
      (η.inv.val ≫ η.hom.val = 𝟙 x'.codomain) ∧
      (x'.hom ≫ Fiber.fiberInclusion.map η.hom.val = x'.hom) := by
    sorry
  ⟨{ hom := η.hom.val
     inv := η.inv.val
     hom_inv_id := laws.1
     inv_hom_id := laws.2.1 }, laws.2.2⟩

/-- A commuting square of square-zero thickenings induces an `A`-linear map
from the infinitesimal automorphisms of a lift to those of its pullback. -/
def infinitesimalAutRestrict {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (x' : liftCat x fA hfA) :
    ModuleCat.of A (infinitesimalAut x') ⟶
      (ModuleCat.restrictScalars v.hom).obj
        (ModuleCat.of B (infinitesimalAut ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).obj x'))) :=
  let g : ModuleCat.of A (infinitesimalAut x') →
      (ModuleCat.restrictScalars v.hom).obj
        (ModuleCat.of B (infinitesimalAut ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).obj x'))) :=
    fun α ↦ infinitesimalAutOfLiftAut ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).obj x')
      ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).mapIso (liftAutOfInfinitesimal x' α))
  have laws : (∀ a b, g (a + b) = g a + g b) ∧
      (∀ (r : A) a, g (r • a) = r • g a) := by
    sorry
  ConcreteCategory.ofHom
    { toFun := g
      map_add' := laws.1
      map_smul' := laws.2 }

/-- Restriction of an infinitesimal automorphism applies the square-induced
pullback functor to its corresponding lift-category automorphism. -/
theorem infinitesimalAutRestrict_apply {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (x' : liftCat x fA hfA) (α : infinitesimalAut x') :
    infinitesimalAutRestrict fA hfA fB hfB v hv u hu sq x y φ x' α =
      infinitesimalAutOfLiftAut ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).obj x')
        ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).mapIso (liftAutOfInfinitesimal x' α)) := by rfl

/-- Push an infinitesimal automorphism of the trivial deformation of `x` along
`A[M] ⟶ B[N]`. -/
def infTypeRestrict {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (α : infType x M) : infType y N :=
  let e := (trivialDeformationRestrictIso v hv f x y φ).symm
  let h := e.hom ≫ Chosen.reindexMap X.p (specOverMapRestrict v hv f) α.1.hom ≫ e.inv
  let i := e.hom ≫ Chosen.reindexMap X.p (specOverMapRestrict v hv f) α.1.inv ≫ e.inv
  have laws : (h ≫ i = 𝟙 (trivialDeformation y N)) ∧
      (i ≫ h = 𝟙 (trivialDeformation y N)) ∧
      ((trivialDeformationLift y N).hom ≫ Fiber.fiberInclusion.map h =
        (trivialDeformationLift y N).hom) := by
    sorry
  ⟨{ hom := h
     inv := i
     hom_inv_id := laws.1
     inv_hom_id := laws.2.1 }, laws.2.2⟩

/-- The canonical `A`-linear map `Inf_x(M) ⟶ Inf_y(N)` induced by `A ⟶ B` and an
`A`-linear map `M ⟶ N`. -/
def infMap {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    (infFunctor x).obj M ⟶
      (ModuleCat.restrictScalars v.hom).obj ((infFunctor y).obj N) :=
  let g : (infFunctor x).obj M →
      (ModuleCat.restrictScalars v.hom).obj ((infFunctor y).obj N) :=
    infTypeRestrict v hv f x y φ
  have laws : (∀ a b, g (a + b) = g a + g b) ∧
      (∀ (r : A) a, g (r • a) = r • g a) := by
    sorry
  ConcreteCategory.ofHom
    { toFun := g
      map_add' := laws.1
      map_smul' := laws.2 }

/-- `infMap` acts by `infTypeRestrict` on infinitesimal automorphisms of the
trivial deformation. -/
theorem infMap_apply {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (α : (infFunctor x).obj M) :
    infMap v hv f x y φ α = infTypeRestrict v hv f x y φ α := by rfl

/-- The canonical `A`-linear map `T_x(M) ⟶ T_y(N)` induced by `A ⟶ B` and an
`A`-linear map `M ⟶ N`. -/
def tangentMap {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    (tangentFunctor x).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} v.hom).obj ((tangentFunctor y).obj N) :=
  let g : (tangentFunctor x).obj M →
      (ModuleCat.restrictScalars.{u + 1} v.hom).obj ((tangentFunctor y).obj N) :=
    fun t ↦ (tangentForget y N).symm
      (liftsMap (trivSqZeroLiftPullback v hv f x y φ) (tangentForget x M t))
  have laws : (∀ a b, g (a + b) = g a + g b) ∧
      (∀ (r : A) a, g (r • a) = r • g a) := by
    sorry
  ConcreteCategory.ofHom
    { toFun := g
      map_add' := laws.1
      map_smul' := laws.2 }

/-- `tangentMap` is `liftsMap` of the trivial-square-zero pullback after
identifying `T_x(M)` with `Lift(x, A[M])`. -/
theorem tangentMap_apply {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (t : (tangentFunctor x).obj M) :
    tangentMap v hv f x y φ t =
      (tangentForget y N).symm
        (liftsMap (trivSqZeroLiftPullback v hv f x y φ) (tangentForget x M t)) :=
  by rfl

/-- Forgetting `T` after `tangentMap` is `liftsMap` of the trivial-square-zero
pullback. -/
theorem tangentForget_tangentMap {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (t : (tangentFunctor x).obj M) :
    tangentForget y N (tangentMap v hv f x y φ t) =
      liftsMap (trivSqZeroLiftPullback v hv f x y φ) (tangentForget x M t) :=
  by rfl

/-- Naturality of `Inf_x(I) ≅ Inf(x'/x)` in a morphism of deformation
situations. Here `y'` is the pullback of the given lift `x'`. -/
theorem infIso_natural {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (x' : liftCat x fA hfA) :
    (infIso x x').hom ≫
        infinitesimalAutRestrict fA hfA fB hfB v hv u hu sq x y φ x' =
      infMap v hv (kernelHom fA fB v u sq) x y φ ≫
        (ModuleCat.restrictScalars v.hom).map
          (infIso y ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).obj x')).hom :=
  sorry

/-- Naturality of the action `T_x(I) × Lift(x, A') ⟶ Lift(x, A')` in a morphism
of deformation situations. -/
theorem tangentAction_natural {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (t : (tangentFunctor x).obj (kernelObj fA))
    (ξ : lifts x fA hfA) :
    liftsMap (liftPullback fA hfA fB hfB v hv u hu sq x y φ) (tangentAction x t ξ) =
      tangentAction y (tangentMap v hv (kernelHom fA fB v u sq) x y φ t)
        (liftsMap (liftPullback fA hfA fB hfB v hv u hu sq x y φ) ξ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
