module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Finite projective modules over Artinian local algebras

The covariant pseudofunctor sending an object `A` of an Artinian local algebra
category to the core of finite projective `A`-modules, together with its
Grothendieck construction.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat.FiniteProjective

/-- Extension of scalars along a morphism of Artinian local algebras preserves finite projectivity. -/
theorem extendScalars_mem {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B)
    (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    ModuleCat.finiteProjective.{u, u} B.carrier
      (((ModuleCat.finiteProjective.{u, u} A.carrier).ι ⋙
        ModuleCat.extendScalars f.toRingHom).obj M) := sorry

/-- Pushforward of finite projective modules along a morphism of Artinian local algebras. -/
def extendScalars {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    ModuleCat.FiniteProjective.{u, u} A.carrier ⥤
      ModuleCat.FiniteProjective.{u, u} B.carrier :=
  (ModuleCat.finiteProjective.{u, u} B.carrier).lift
    ((ModuleCat.finiteProjective.{u, u} A.carrier).ι ⋙
      ModuleCat.extendScalars f.toRingHom)
    (extendScalars_mem f)

/-- Identity morphisms act on finite projective modules by the canonical identity comparison. -/
def extendScalarsId (A : ArtinianLocalAlgCat Λ k) :
    extendScalars (𝟙 A) ≅ 𝟭 (ModuleCat.FiniteProjective.{u, u} A.carrier) :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk (ModuleCat.finiteProjective A.carrier)
      ((ModuleCat.extendScalarsId A.carrier).app M.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((ModuleCat.extendScalarsId A.carrier).hom.naturality φ.hom))

/-- The underlying module map of the identity scalar-extension comparison. -/
theorem extendScalarsId_hom_app (A : ArtinianLocalAlgCat Λ k)
    (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    ((extendScalarsId A).hom.app M).hom =
      (ModuleCat.extendScalarsId A.carrier).hom.app M.obj := rfl

/-- Composite morphisms act by the canonical composite scalar-extension comparison. -/
def extendScalarsComp {A B C : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    extendScalars (f ≫ g) ≅ extendScalars f ⋙ extendScalars g :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk (ModuleCat.finiteProjective C.carrier)
      ((ModuleCat.extendScalarsComp f.toRingHom g.toRingHom).app M.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((ModuleCat.extendScalarsComp f.toRingHom g.toRingHom).hom.naturality φ.hom))

/-- The underlying module map of the composite scalar-extension comparison. -/
theorem extendScalarsComp_hom_app {A B C : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ B) (g : B ⟶ C) (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    ((extendScalarsComp f g).hom.app M).hom =
      (ModuleCat.extendScalarsComp f.toRingHom g.toRingHom).hom.app M.obj := rfl

/-- Associativity coherence for the core-valued scalar-extension pseudofunctor. -/
theorem coreExtendScalars_assoc {A B C D : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (Cat.Hom.isoMk (Iso.core (extendScalarsComp (f ≫ g) h))).hom ≫
        (Cat.Hom.isoMk (Iso.core (extendScalarsComp f g))).hom ▷
          (Functor.core (extendScalars h)).toCatHom ≫
          (α_ ((Functor.core (extendScalars f)).toCatHom)
            ((Functor.core (extendScalars g)).toCatHom)
            ((Functor.core (extendScalars h)).toCatHom)).hom ≫
            (Functor.core (extendScalars f)).toCatHom ◁
              (Cat.Hom.isoMk (Iso.core (extendScalarsComp g h))).inv ≫
                (Cat.Hom.isoMk (Iso.core (extendScalarsComp f (g ≫ h)))).inv =
      eqToHom (by simp) := sorry

/-- Left-unit coherence for the core-valued scalar-extension pseudofunctor. -/
theorem coreExtendScalars_id_comp {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    (Cat.Hom.isoMk (Iso.core (extendScalarsComp (𝟙 A) f))).hom ≫
        (Cat.Hom.isoMk (Iso.core (extendScalarsId A) ≪≫ Functor.coreId _)).hom ▷
          (Functor.core (extendScalars f)).toCatHom ≫
            (λ_ ((Functor.core (extendScalars f)).toCatHom)).hom =
      eqToHom (by simp) := sorry

/-- Right-unit coherence for the core-valued scalar-extension pseudofunctor. -/
theorem coreExtendScalars_comp_id {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    (Cat.Hom.isoMk (Iso.core (extendScalarsComp f (𝟙 B)))).hom ≫
        (Functor.core (extendScalars f)).toCatHom ◁
          (Cat.Hom.isoMk (Iso.core (extendScalarsId B) ≪≫ Functor.coreId _)).hom ≫
            (ρ_ ((Functor.core (extendScalars f)).toCatHom)).hom =
      eqToHom (by simp) := sorry

/-- The core-valued pseudofunctor of finite projective scalar extension. -/
def pseudofunctor (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] :
    LocallyDiscrete (ArtinianLocalAlgCat Λ k) ⥤ᵖ Cat.{u, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun A ↦ Cat.of (Core (ModuleCat.FiniteProjective.{u, u} A.carrier)))
    (fun f ↦ (Functor.core (extendScalars f)).toCatHom)
    (fun A ↦ Cat.Hom.isoMk (Iso.core (extendScalarsId A) ≪≫ Functor.coreId _))
    (fun f g ↦ Cat.Hom.isoMk (Iso.core (extendScalarsComp f g)))
    (fun f g h ↦ coreExtendScalars_assoc f g h)
    (fun f ↦ coreExtendScalars_id_comp f)
    (fun f ↦ coreExtendScalars_comp_id f)

/-- The object value of the finite-projective scalar-extension pseudofunctor. -/
theorem pseudofunctor_obj (A : ArtinianLocalAlgCat Λ k) :
    (pseudofunctor Λ k).obj ⟨A⟩ =
      Cat.of (Core (ModuleCat.FiniteProjective.{u, u} A.carrier)) := rfl

/-- The morphism value of the finite-projective scalar-extension pseudofunctor. -/
theorem pseudofunctor_map {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    ((pseudofunctor Λ k).map f.toLoc).toFunctor = Functor.core (extendScalars f) := rfl

/-- The Grothendieck projection of finite projective modules is cofibered in groupoids. -/
instance instInGroupoids_forget (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k] :
    Functor.IsFibered.InGroupoids
      (Pseudofunctor.Grothendieck.forget (pseudofunctor Λ k)).op := sorry

/-- The category of finite projective modules over Artinian local algebras. -/
def groupoids (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (Pseudofunctor.Grothendieck.forget (pseudofunctor Λ k))

/-- The projection of the finite-projective category is its Grothendieck projection. -/
theorem groupoids_p :
    (groupoids Λ k).p = Pseudofunctor.Grothendieck.forget (pseudofunctor Λ k) := rfl

/-- The total category of finite projective modules is its Grothendieck construction. -/
theorem groupoids_total :
    (groupoids Λ k).total = Pseudofunctor.Grothendieck (pseudofunctor Λ k) := rfl

/-- An object of the finite-projective category is a base algebra and a finite projective module. -/
def mkObj (A : ArtinianLocalAlgCat Λ k) (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    (groupoids Λ k).total :=
  ⟨A, Core.mk M⟩

/-- A morphism is a base map together with an isomorphism after scalar extension. -/
def mkHom {B A : ArtinianLocalAlgCat Λ k}
    {N : ModuleCat.FiniteProjective.{u, u} B.carrier}
    {M : ModuleCat.FiniteProjective.{u, u} A.carrier}
    (f : B ⟶ A) (e : (extendScalars f).obj N ≅ M) :
    mkObj B N ⟶ mkObj A M where
  base := f
  fiber := CoreHom.mk e

/-- The projection sends a constructed object to its base algebra. -/
theorem p_obj (A : ArtinianLocalAlgCat Λ k)
    (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    (groupoids Λ k).p.obj (mkObj A M) = A := rfl

/-- The projection sends a Grothendieck morphism to its base map. -/
theorem p_map {X Y : (groupoids Λ k).total} (φ : X ⟶ Y) :
    (groupoids Λ k).p.map φ = φ.base := rfl

/-- A constructed object lies over its base and has the specified fibre object. -/
theorem obj_spec (A : ArtinianLocalAlgCat Λ k)
    (M : ModuleCat.FiniteProjective.{u, u} A.carrier) :
    (groupoids Λ k).p.obj (mkObj A M) = A ∧ (mkObj A M).fiber = Core.mk M := ⟨rfl, rfl⟩

/-- A morphism is determined by its base map and a scalar-extension isomorphism. -/
theorem hom_spec {B A : ArtinianLocalAlgCat Λ k}
    {N : ModuleCat.FiniteProjective.{u, u} B.carrier}
    {M : ModuleCat.FiniteProjective.{u, u} A.carrier}
    (φ : mkObj B N ⟶ mkObj A M) :
    ∃ e : (extendScalars φ.base).obj N ≅ M, φ = mkHom φ.base e := ⟨φ.fiber.iso, rfl⟩

/-- Package a semilinear map with invertible scalar-extension transpose as a morphism. -/
def mkHomOfLinear {B A : ArtinianLocalAlgCat Λ k}
    {N : ModuleCat.FiniteProjective.{u, u} B.carrier}
    {M : ModuleCat.FiniteProjective.{u, u} A.carrier}
    (f : B ⟶ A)
    (g : N.obj ⟶ (ModuleCat.restrictScalars f.toRingHom).obj M.obj)
    (hg : IsIso (((ModuleCat.extendRestrictScalarsAdj f.toRingHom).homEquiv
      N.obj M.obj).symm g)) :
    mkObj B N ⟶ mkObj A M :=
  mkHom f
    (ObjectProperty.isoMk (ModuleCat.finiteProjective A.carrier)
      (@asIso _ _ _ _ (((ModuleCat.extendRestrictScalarsAdj f.toRingHom).homEquiv
        N.obj M.obj).symm g) hg))

/-- Every morphism is represented by a semilinear map with invertible transpose. -/
theorem mkHomOfLinear_spec {B A : ArtinianLocalAlgCat Λ k}
    {N : ModuleCat.FiniteProjective.{u, u} B.carrier}
    {M : ModuleCat.FiniteProjective.{u, u} A.carrier}
    (φ : mkObj B N ⟶ mkObj A M) :
    ∃ (g : N.obj ⟶ (ModuleCat.restrictScalars φ.base.toRingHom).obj M.obj)
      (hg : IsIso (((ModuleCat.extendRestrictScalarsAdj φ.base.toRingHom).homEquiv
        N.obj M.obj).symm g)),
      φ = mkHomOfLinear φ.base g hg := sorry

/-- Reconstruct a fibre object from a finite projective module. -/
def coreToFiber (A : ArtinianLocalAlgCat Λ k)
    (M : Core (ModuleCat.FiniteProjective.{u, u} A.carrier)) :
    (groupoids Λ k).p.Fiber A :=
  ⟨mkObj A M.of, rfl⟩

/-- Extract a finite projective module from a fibre object. -/
def fiberToCore (A : ArtinianLocalAlgCat Λ k) (x : (groupoids Λ k).p.Fiber A) :
    Core (ModuleCat.FiniteProjective.{u, u} A.carrier) :=
  x.property ▸ x.1.fiber

/-- Reconstructing a fibre object from its extracted module returns the original object. -/
theorem coreToFiber_fiberToCore (A : ArtinianLocalAlgCat Λ k)
    (x : (groupoids Λ k).p.Fiber A) :
    coreToFiber A (fiberToCore A x) = x := sorry

/-- Extracting a module after reconstructing its fibre object returns the original module. -/
theorem fiberToCore_coreToFiber (A : ArtinianLocalAlgCat Λ k)
    (M : Core (ModuleCat.FiniteProjective.{u, u} A.carrier)) :
    fiberToCore A (coreToFiber A M) = M := rfl

end ArtinianLocalAlgCat.FiniteProjective
