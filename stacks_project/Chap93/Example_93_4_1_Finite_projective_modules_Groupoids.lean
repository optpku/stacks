module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.RingTheory.Finiteness.Projective.BaseChange
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids

/-!
# Finite projective modules over Artinian local algebras

The covariant pseudofunctor sending an object `A` of `C_Λ` to the core of finite
projective `A`-modules, and the associated Grothendieck category cofibered in
groupoids. Extension of scalars is only pseudo-functorial, so the owner is
`Pseudofunctor.Grothendieck` rather than a strict `C ⥤ Grpd`.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat.FiniteProjective

/-- Extension of scalars along a morphism of `C_Λ` preserves finite projectivity. -/
theorem extendScalars_mem {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B)
    (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    ModuleCat.finiteProjective.{u, u} B.carrier
      (((ModuleCat.finiteProjective.{u, u} A.carrier).ι ⋙
        ModuleCat.extendScalars f.hom.toRingHom).obj M) := sorry

/-- Pushforward of finite projective modules along a morphism `f : A ⟶ B` of `C_Λ`. -/
def extendScalars {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    ModuleCat.FiniteProjective.{u, u} A.carrier ⥤
      ModuleCat.FiniteProjective.{u, u} B.carrier :=
  (ModuleCat.finiteProjective.{u, u} B.carrier).lift
    ((ModuleCat.finiteProjective.{u, u} A.carrier).ι ⋙
      ModuleCat.extendScalars f.hom.toRingHom)
    (extendScalars_mem f)

/-- Identity morphisms of `C_Λ` act as the identity up to the canonical
`ModuleCat.extendScalarsId` isomorphism. -/
def extendScalarsId (A : ArtinianLocalAlgCat Λ k) :
    extendScalars (𝟙 A) ≅ 𝟭 (ModuleCat.FiniteProjective.{u, u} A.carrier) :=
  NatIso.ofComponents
    (fun M ↦
      { hom := ObjectProperty.homMk ((ModuleCat.extendScalarsId A.carrier).hom.app M.obj)
        inv := ObjectProperty.homMk ((ModuleCat.extendScalarsId A.carrier).inv.app M.obj)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The underlying module map of `extendScalarsId` is `ModuleCat.extendScalarsId`. -/
theorem extendScalarsId_hom_app (A : ArtinianLocalAlgCat Λ k)
    (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    ((extendScalarsId A).hom.app M).hom =
      (ModuleCat.extendScalarsId A.carrier).hom.app M.obj := sorry

/-- Composite morphisms of `C_Λ` act as the composite of extension-of-scalars functors,
up to the canonical `ModuleCat.extendScalarsComp` isomorphism. -/
def extendScalarsComp {A B C : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    extendScalars (f ≫ g) ≅ extendScalars f ⋙ extendScalars g :=
  NatIso.ofComponents
    (fun M ↦
      { hom := ObjectProperty.homMk
          ((ModuleCat.extendScalarsComp f.hom.toRingHom g.hom.toRingHom).hom.app M.obj)
        inv := ObjectProperty.homMk
          ((ModuleCat.extendScalarsComp f.hom.toRingHom g.hom.toRingHom).inv.app M.obj)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The underlying module map of `extendScalarsComp` is `ModuleCat.extendScalarsComp`. -/
theorem extendScalarsComp_hom_app {A B C : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ B) (g : B ⟶ C) (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    ((extendScalarsComp f g).hom.app M).hom =
      (ModuleCat.extendScalarsComp f.hom.toRingHom g.hom.toRingHom).hom.app M.obj :=
  sorry

/-- The covariant pseudofunctor sending `A` to the core of finite projective `A`-modules,
with transition functors given by extension of scalars. -/
def pseudofunctor (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] :
    LocallyDiscrete (ArtinianLocalAlgCat Λ k) ⥤ᵖ Cat.{u, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun A ↦ Cat.of (Core (ModuleCat.FiniteProjective.{u, u} A.carrier)))
    (fun f ↦ (Functor.core (extendScalars f)).toCatHom)
    (fun A ↦
      Cat.Hom.isoMk (Iso.core (extendScalarsId A) ≪≫ Functor.coreId _))
    (fun f g ↦ Cat.Hom.isoMk (Iso.core (extendScalarsComp f g)))
    sorry
    sorry
    sorry

/-- The fibre of `pseudofunctor` at `A` is the core of finite projective `A`-modules. -/
theorem pseudofunctor_obj (A : ArtinianLocalAlgCat Λ k) :
    (pseudofunctor Λ k).obj ⟨A⟩ =
      Cat.of (Core (ModuleCat.FiniteProjective.{u, u} A.carrier)) := sorry

/-- `pseudofunctor` pushes finite projective modules forward by `extendScalars`. -/
theorem pseudofunctor_map {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    ((pseudofunctor Λ k).map f.toLoc).toFunctor = Functor.core (extendScalars f) :=
  sorry

/-- The Grothendieck projection of finite projective modules is cofibered in groupoids. -/
instance instInGroupoids_forget (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k] :
    Functor.IsFibered.InGroupoids
      (Pseudofunctor.Grothendieck.forget (pseudofunctor Λ k)).op := sorry

/-- The category `F` of finite projective modules over objects of `C_Λ`, cofibered in
groupoids over `C_Λ`. -/
def groupoids (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (Pseudofunctor.Grothendieck.forget (pseudofunctor Λ k))

/-- The projection of `groupoids` is the pseudofunctor Grothendieck forgetful functor. -/
theorem groupoids_p :
    (groupoids Λ k).p = Pseudofunctor.Grothendieck.forget (pseudofunctor Λ k) := sorry

/-- The total category of `groupoids` is the Grothendieck construction of `pseudofunctor`. -/
theorem groupoids_total :
    (groupoids Λ k).total = Pseudofunctor.Grothendieck (pseudofunctor Λ k) := sorry

/-- An object of `F` is a pair `(A, M)` with `M` a finite projective `A`-module. -/
def mkObj (A : ArtinianLocalAlgCat Λ k) (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    (groupoids Λ k).total :=
  ⟨A, Core.mk M⟩

/-- A morphism `(B, N) ⟶ (A, M)` in `F` is a map `f : B ⟶ A` together with an isomorphism
`(extendScalars f).obj N ≅ M`. -/
def mkHom {B A : ArtinianLocalAlgCat Λ k}
    {N : ModuleCat.FiniteProjective.{u, u} B.carrier}
    {M : ModuleCat.FiniteProjective.{u, u} A.carrier}
    (f : B ⟶ A) (e : (extendScalars f).obj N ≅ M) :
    mkObj B N ⟶ mkObj A M where
  base := f
  fiber := CoreHom.mk e

/-- The projection of `F` sends `(A, M)` to `A`. -/
theorem p_obj (A : ArtinianLocalAlgCat Λ k)
    (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    (groupoids Λ k).p.obj (mkObj A M) = A := sorry

/-- The projection of `F` sends a Grothendieck morphism to its base map. -/
theorem p_map {X Y : (groupoids Λ k).total} (φ : X ⟶ Y) :
    (groupoids Λ k).p.map φ = φ.base := sorry

/-- The object `(A, M)` lies over `A`, with fibre the given finite projective module. -/
theorem obj_spec (A : ArtinianLocalAlgCat Λ k)
    (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    (groupoids Λ k).p.obj (mkObj A M) = A ∧ (mkObj A M).fiber = Core.mk M := sorry

/-- A morphism of `F` is a base map together with an isomorphism after extension of scalars. -/
theorem hom_spec {B A : ArtinianLocalAlgCat Λ k}
    {N : ModuleCat.FiniteProjective.{u, u} B.carrier}
    {M : ModuleCat.FiniteProjective.{u, u} A.carrier}
    (φ : mkObj B N ⟶ mkObj A M) :
    ∃ e : (extendScalars φ.base).obj N ≅ M, φ = mkHom φ.base e := sorry

/-- Package an `f`-linear map inducing `N ⊗_{B, f} A ≅ M` as a morphism of `F`. -/
def mkHomOfLinear {B A : ArtinianLocalAlgCat Λ k}
    {N : ModuleCat.FiniteProjective.{u, u} B.carrier}
    {M : ModuleCat.FiniteProjective.{u, u} A.carrier}
    (f : B ⟶ A)
    (g : N.obj ⟶ (ModuleCat.restrictScalars f.hom.toRingHom).obj M.obj)
    (hg : IsIso (((ModuleCat.extendRestrictScalarsAdj f.hom.toRingHom).homEquiv
      N.obj M.obj).symm g)) :
    mkObj B N ⟶ mkObj A M :=
  mkHom f
    { hom := ObjectProperty.homMk
        (((ModuleCat.extendRestrictScalarsAdj f.hom.toRingHom).homEquiv N.obj M.obj).symm g)
      inv := ObjectProperty.homMk
        (@CategoryTheory.inv _ _ _ _
          (((ModuleCat.extendRestrictScalarsAdj f.hom.toRingHom).homEquiv N.obj M.obj).symm g)
          hg)
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Every morphism `(B, N) ⟶ (A, M)` in `F` arises from an `f`-linear map inducing
`N ⊗_{B, f} A ≅ M`. -/
theorem mkHomOfLinear_spec {B A : ArtinianLocalAlgCat Λ k}
    {N : ModuleCat.FiniteProjective.{u, u} B.carrier}
    {M : ModuleCat.FiniteProjective.{u, u} A.carrier}
    (φ : mkObj B N ⟶ mkObj A M) :
    ∃ (g : N.obj ⟶ (ModuleCat.restrictScalars φ.base.hom.toRingHom).obj M.obj)
      (hg : IsIso (((ModuleCat.extendRestrictScalarsAdj φ.base.hom.toRingHom).homEquiv
        N.obj M.obj).symm g)),
      φ = mkHomOfLinear φ.base g hg := sorry

/-- Reconstruct a fibre object over `A` from a finite projective `A`-module. -/
def coreToFiber (A : ArtinianLocalAlgCat Λ k)
    (M : Core (ModuleCat.FiniteProjective.{u, u} A.carrier)) :
    (groupoids Λ k).p.Fiber A :=
  ⟨mkObj A M.of, rfl⟩

/-- Extract the finite projective module from a fibre object over `A`. -/
def fiberToCore (A : ArtinianLocalAlgCat Λ k) (x : (groupoids Λ k).p.Fiber A) :
    Core (ModuleCat.FiniteProjective.{u, u} A.carrier) :=
  x.property ▸ x.1.fiber

/-- The fibre of `p` over `A` is equivalent to the core of finite projective `A`-modules. -/
theorem fiberEquiv (A : ArtinianLocalAlgCat Λ k)
    (x : (groupoids Λ k).p.Fiber A) :
    coreToFiber A (fiberToCore A x) = x := sorry

/-- Going from a finite projective module to the fibre and back is the identity. -/
theorem fiberEquiv_symm (A : ArtinianLocalAlgCat Λ k)
    (M : Core (ModuleCat.FiniteProjective.{u, u} A.carrier)) :
    fiberToCore A (coreToFiber A M) = M := sorry

end ArtinianLocalAlgCat.FiniteProjective
