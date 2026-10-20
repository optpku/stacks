module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FrobeniusColimit
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.GroupoidValued
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Basic

/-!
# Finite locally free modules over Frobenius-colimit structure sheaves

This module constructs the groupoid-valued pseudofunctor of finite locally free modules over
Frobenius-colimit structure sheaves and its co-Grothendieck fibered category.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Bicategory

universe u

namespace AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit

/-- The core of finite locally free modules over the Frobenius-colimit structure sheaf of a
scheme represented in the chosen big slice. -/
def moduleCategory (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    Cat.{u + 1, u + 1} :=
  -- Local instance justification (search instability): derive the represented scheme's characteristic only while constructing its fibre.
  letI : Scheme.IsCharP ((ChosenBigSite.sliceToScheme Schh S).obj U) p :=
    Scheme.Hom.isCharP_of_target (Schh.toScheme.map U.hom)
  Cat.of (Core (Scheme.FrobeniusColimit.finiteLocallyFreeModules p
    ((ChosenBigSite.sliceToScheme Schh S).obj U)))

/-- Pullback of finite locally free Frobenius-colimit modules along a morphism in the chosen
big slice, restricted to the cores. -/
def moduleReindex (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V : Over S} (f : U ⟶ V) :
    moduleCategory p Schh S V ⥤ moduleCategory p Schh S U :=
  -- Local instance justification (search instability): derive the source characteristic only while constructing this pullback functor.
  letI : Scheme.IsCharP ((ChosenBigSite.sliceToScheme Schh S).obj U) p :=
    Scheme.Hom.isCharP_of_target (Schh.toScheme.map U.hom)
  -- Local instance justification (search instability): derive the target characteristic only while constructing this pullback functor.
  letI : Scheme.IsCharP ((ChosenBigSite.sliceToScheme Schh S).obj V) p :=
    Scheme.Hom.isCharP_of_target (Schh.toScheme.map V.hom)
  (Scheme.FrobeniusColimit.ModuleModel.pullback p
    ((ChosenBigSite.sliceToScheme Schh S).map f)).core

/-- Reindexing the core of finite locally free Frobenius-colimit modules along an identity in
the chosen big slice is the identity functor. -/
theorem moduleReindex_id (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    moduleReindex p Schh S (𝟙 U) = 𝟭 (moduleCategory p Schh S U) := sorry

/-- The identity comparison for core-valued reindexing on the chosen big slice. -/
def moduleReindexIdIso (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    (moduleReindex p Schh S (𝟙 U)).toCatHom ≅
      (𝟭 (moduleCategory p Schh S U)).toCatHom :=
  Cat.Hom.isoMk (eqToIso (moduleReindex_id p Schh S U))

/-- The identity comparison is induced by the canonical identity equality for module
reindexing. -/
theorem moduleReindexIdIso_toNatIso (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    Cat.Hom.toNatIso (moduleReindexIdIso p Schh S U) =
      eqToIso (moduleReindex_id p Schh S U) := sorry

/-- Reindexing along a composite in the opposite chosen big slice is the composite of the two
core-valued reindexing functors. -/
theorem moduleReindex_comp (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V W : (Over S)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    moduleReindex p Schh S (f ≫ g).unop =
      moduleReindex p Schh S f.unop ⋙ moduleReindex p Schh S g.unop := sorry

/-- The composition comparison for core-valued reindexing on the chosen big slice. -/
def moduleReindexCompIso (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V W : (Over S)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    (moduleReindex p Schh S (f ≫ g).unop).toCatHom ≅
      (moduleReindex p Schh S f.unop ⋙ moduleReindex p Schh S g.unop).toCatHom :=
  Cat.Hom.isoMk (eqToIso (moduleReindex_comp p Schh S f g))

/-- The composition comparison is induced by the canonical composition equality for module
reindexing. -/
theorem moduleReindexCompIso_toNatIso (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V W : (Over S)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    Cat.Hom.toNatIso (moduleReindexCompIso p Schh S f g) =
      eqToIso (moduleReindex_comp p Schh S f g) := sorry

/-- Reindexing identifies the two parenthesizations of a triple composite. -/
theorem moduleReindex_assoc (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V W T : (Over S)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ T) :
    (moduleReindex p Schh S ((f ≫ g) ≫ h).unop).toCatHom =
      (moduleReindex p Schh S (f ≫ (g ≫ h)).unop).toCatHom := sorry

/-- Reindexing along an identity followed by a morphism identifies with reindexing along the
morphism. -/
theorem moduleReindex_leftUnit (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (moduleReindex p Schh S ((𝟙 U) ≫ f).unop).toCatHom =
      (moduleReindex p Schh S f.unop).toCatHom := sorry

/-- Reindexing along a morphism followed by an identity identifies with reindexing along the
morphism. -/
theorem moduleReindex_rightUnit (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (moduleReindex p Schh S (f ≫ 𝟙 V).unop).toCatHom =
      (moduleReindex p Schh S f.unop).toCatHom := sorry

/-- The restricted module-pullback comparisons satisfy associativity. -/
theorem moduleReindex_associator (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V W T : (Over S)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ T) :
    (moduleReindexCompIso p Schh S (f ≫ g) h).hom ≫
        (moduleReindexCompIso p Schh S f g).hom ▷
          (moduleReindex p Schh S h.unop).toCatHom ≫
      (α_
        (moduleReindex p Schh S f.unop).toCatHom
        (moduleReindex p Schh S g.unop).toCatHom
        (moduleReindex p Schh S h.unop).toCatHom).hom ≫
      (moduleReindex p Schh S f.unop).toCatHom ◁
          (moduleReindexCompIso p Schh S g h).inv ≫
      (moduleReindexCompIso p Schh S f (g ≫ h)).inv =
        eqToHom (moduleReindex_assoc p Schh S f g h) := sorry

/-- The restricted module-pullback comparisons satisfy left-unit coherence. -/
theorem moduleReindex_leftUnitor (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (moduleReindexCompIso p Schh S (𝟙 U) f).hom ≫
        (moduleReindexIdIso p Schh S U.unop).hom ▷
          (moduleReindex p Schh S f.unop).toCatHom ≫
      (λ_ (moduleReindex p Schh S f.unop).toCatHom).hom =
        eqToHom (moduleReindex_leftUnit p Schh S f) := sorry

/-- The restricted module-pullback comparisons satisfy right-unit coherence. -/
theorem moduleReindex_rightUnitor (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (moduleReindexCompIso p Schh S f (𝟙 V)).hom ≫
        (moduleReindex p Schh S f.unop).toCatHom ◁
          (moduleReindexIdIso p Schh S V.unop).hom ≫
      (ρ_ (moduleReindex p Schh S f.unop).toCatHom).hom =
        eqToHom (moduleReindex_rightUnit p Schh S f) := sorry

/-- The Cat-valued pseudofunctor underlying Frobenius-colimit module reindexing. -/
def modulePseudofunctorRaw (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun U ↦ moduleCategory p Schh S U.unop)
    (fun f ↦ (moduleReindex p Schh S f.unop).toCatHom)
    (fun U ↦ moduleReindexIdIso p Schh S U.unop)
    (fun f g ↦ moduleReindexCompIso p Schh S f g)
    (moduleReindex_associator p Schh S)
    (moduleReindex_leftUnitor p Schh S)
    (moduleReindex_rightUnitor p Schh S)

/-- Every value of `modulePseudofunctorRaw` is a groupoid. -/
theorem modulePseudofunctorRawIsGroupoid (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    ∀ U, IsGroupoid ((modulePseudofunctorRaw p Schh S).obj U) := sorry

/-- The groupoid-valued pseudofunctor of finite locally free modules over the
Frobenius-colimit structure sheaves of objects of the chosen big slice. -/
def modulePseudofunctor (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Pseudofunctor.GroupoidValued (Over S) :=
  -- Local instance justification (search instability): install pointwise groupoidality only while bundling this pseudofunctor.
  letI : ∀ U, IsGroupoid ((modulePseudofunctorRaw p Schh S).obj U) :=
    modulePseudofunctorRawIsGroupoid p Schh S
  Pseudofunctor.GroupoidValued.mk (modulePseudofunctorRaw p Schh S)

/-- The object value of `modulePseudofunctor` is the core of finite locally free modules over
the represented Frobenius-colimit sheaf. -/
theorem modulePseudofunctor_obj (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    (modulePseudofunctor p Schh S).toPseudofunctor.obj ⟨op U⟩ =
      moduleCategory p Schh S U := sorry

/-- The morphism action of `modulePseudofunctor` is restricted module pullback followed by
passage to the core. -/
theorem modulePseudofunctor_map (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] {U V : Over S} (f : U ⟶ V) :
    ((modulePseudofunctor p Schh S).toPseudofunctor.map f.op.toLoc).toFunctor =
      moduleReindex p Schh S f := sorry

/-- The co-Grothendieck realization of finite locally free modules over the
Frobenius-colimit structure sheaves. -/
def moduleFiberedCategory (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    FiberedCategoryOver.Groupoids (Over S) :=
  Pseudofunctor.CoGrothendieck.toFibered
    (modulePseudofunctor p Schh S).toPseudofunctor

/-- The projection of `moduleFiberedCategory` is the canonical co-Grothendieck projection. -/
theorem moduleFiberedCategory_p (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    (moduleFiberedCategory p Schh S).p = Pseudofunctor.CoGrothendieck.forget
      (modulePseudofunctor p Schh S).toPseudofunctor := sorry

/-- The standard fibre of `moduleFiberedCategory` is canonically equivalent to the core of
finite locally free modules over the represented Frobenius-colimit sheaf. -/
def moduleFiberEquiv (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    (moduleFiberedCategory p Schh S).p.Fiber U ≌ moduleCategory p Schh S U :=
  (Functor.asEquivalence
    (Functor.Fiber.inducedFunctor
      (Pseudofunctor.CoGrothendieck.comp_const
        (modulePseudofunctor p Schh S).toPseudofunctor U))).symm

/-- The fibre equivalence is induced by the canonical co-Grothendieck fibre functor. -/
theorem moduleFiberEquiv_inverse (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    (moduleFiberEquiv p Schh S U).inverse =
      Functor.Fiber.inducedFunctor
        (Pseudofunctor.CoGrothendieck.comp_const
          (modulePseudofunctor p Schh S).toPseudofunctor U) := sorry

end AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit
