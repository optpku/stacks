/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Restriction of a based category over `Ĉ_Λ` along `C_Λ ↪ Ĉ_Λ`

Objects of `BasedCategory.RestrictInclusion X` are objects of a based category `X` over
`CompleteLocalAlgCat Λ k` whose base is the image of an Artinian algebra. This is the
strict pullback of `X.p` along `ArtinianLocalAlgCat.inclusion`.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedCategory

/-- An object of `X` lying strictly over the image of an Artinian algebra under
`ArtinianLocalAlgCat.inclusion`. -/
def RestrictInclusion
    (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :=
  Σ' obj : X.obj, Σ' base : ArtinianLocalAlgCat Λ k, X.p.obj obj = toComplete base

namespace RestrictInclusion

variable {X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}

/-- The underlying object of a restriction. -/
def obj (ξ : RestrictInclusion X) : X.obj := ξ.1
/-- The Artinian base of a restriction. -/
def base (ξ : RestrictInclusion X) : ArtinianLocalAlgCat Λ k := ξ.2.1
/-- The stored projection identification. -/
theorem over (ξ : RestrictInclusion X) : X.p.obj ξ.obj = toComplete ξ.base := ξ.2.2

/-- Package an object of `X` lying over `toComplete A` as a restricted object. -/
def of (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) : RestrictInclusion X := ⟨obj, base, over⟩

/-- The underlying object of a packaged restriction is the supplied object. -/
theorem of_obj (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) :
    (of obj base over).obj = obj := rfl

/-- The Artinian base of a packaged restriction is the supplied algebra. -/
theorem of_base (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) :
    (of obj base over).base = base := rfl

/-- A restricted object lies over `toComplete` of its Artinian base. -/
theorem spec (ξ : RestrictInclusion X) : X.p.obj ξ.obj = toComplete ξ.base := ξ.over

/-- A morphism of restricted objects is an arrow together with a compatible Artinian base map. -/
def Hom (ξ η : RestrictInclusion X) :=
  Σ' obj : ξ.obj ⟶ η.obj, Σ' base : ξ.base ⟶ η.base,
    inclusion.map base = eqToHom ξ.over.symm ≫ X.p.map obj ≫ eqToHom η.over

private def categoricalHom (ξ η : RestrictInclusion X) := Hom ξ η

/-- The underlying arrow of a restricted morphism. -/
def Hom.obj {ξ η : RestrictInclusion X} (a : Hom ξ η) : ξ.obj ⟶ η.obj := a.1
/-- The base arrow of a restricted morphism. -/
def Hom.base {ξ η : RestrictInclusion X} (a : Hom ξ η) : ξ.base ⟶ η.base := a.2.1
/-- The compatibility of a restricted morphism with its projection. -/
theorem Hom.over {ξ η : RestrictInclusion X} (a : Hom ξ η) :
    inclusion.map a.base = eqToHom ξ.over.symm ≫ X.p.map a.obj ≫ eqToHom η.over := a.2.2
/-- Construct a morphism from its compatible components. -/
def Hom.of {ξ η : RestrictInclusion X} (obj : ξ.obj ⟶ η.obj) (base : ξ.base ⟶ η.base)
    (over : inclusion.map base = eqToHom ξ.over.symm ≫ X.p.map obj ≫ eqToHom η.over) :
    Hom ξ η := ⟨obj, base, over⟩

/-- Restricted arrows are determined by their underlying arrow and base arrow. -/
@[ext]
theorem Hom.ext {ξ η : RestrictInclusion X} {a b : Hom ξ η}
    (hobj : a.obj = b.obj) (hbase : a.base = b.base) : a = b := by
  rcases a with ⟨a, a₀, ha⟩
  rcases b with ⟨b, b₀, hb⟩
  change a = b at hobj
  change a₀ = b₀ at hbase
  cases hobj
  cases hbase
  rfl

/-- The identity arrows satisfy the compatibility with the base projection. -/
theorem Hom.id_laws (ξ : RestrictInclusion X) :
    inclusion.map (𝟙 ξ.base) = eqToHom ξ.over.symm ≫ X.p.map (𝟙 ξ.obj) ≫ eqToHom ξ.over := by
  simp [inclusion]

/-- Identity morphism of a restricted object. -/
def Hom.id (ξ : RestrictInclusion X) : Hom ξ ξ :=
  Hom.of (𝟙 ξ.obj) (𝟙 ξ.base) (Hom.id_laws ξ)

/-- Composition preserves compatibility with the base projection. -/
theorem Hom.comp_laws {ξ η ζ : RestrictInclusion X} (a : Hom ξ η) (b : Hom η ζ) :
    inclusion.map (a.base ≫ b.base) =
      eqToHom ξ.over.symm ≫ X.p.map (a.obj ≫ b.obj) ≫ eqToHom ζ.over := by
  rw [Functor.map_comp, a.over, b.over, X.p.map_comp]
  dsimp only [inclusion]
  simp [Category.assoc]

/-- Composition of morphisms of restricted objects. -/
def Hom.comp {ξ η ζ : RestrictInclusion X} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ :=
  Hom.of (a.obj ≫ b.obj) (a.base ≫ b.base) (Hom.comp_laws a b)

/-- A restricted morphism is compatible with inclusion of Artinian bases. -/
theorem Hom.spec {ξ η : RestrictInclusion X} (a : Hom ξ η) :
    inclusion.map a.base = eqToHom ξ.over.symm ≫ X.p.map a.obj ≫ eqToHom η.over := a.over

/-- Restricted identities and composition satisfy the category laws. -/
theorem category_laws :
    (∀ (ξ η : RestrictInclusion X) (f : Hom ξ η), Hom.comp (Hom.id ξ) f = f) ∧
    (∀ (ξ η : RestrictInclusion X) (f : Hom ξ η), Hom.comp f (Hom.id η) = f) ∧
    (∀ (ξ η ζ θ : RestrictInclusion X) (f : Hom ξ η) (g : Hom η ζ) (h : Hom ζ θ),
      Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ξ η f
    exact Hom.ext (Category.id_comp f.obj) (Category.id_comp f.base)
  · intro ξ η f
    exact Hom.ext (Category.comp_id f.obj) (Category.comp_id f.base)
  · intro ξ η ζ θ f g h
    exact Hom.ext (Category.assoc f.obj g.obj h.obj) (Category.assoc f.base g.base h.base)

private abbrev categoricalStructure : Category.{max u v} (RestrictInclusion X) where
  Hom := categoricalHom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := category_laws.1 _ _
  comp_id := category_laws.2.1 _ _
  assoc := category_laws.2.2 _ _ _ _

/-- Category of objects of `X` restricted to Artinian bases. -/
instance category : Category.{max u v} (RestrictInclusion X) := categoricalStructure

/-- Projection of restricted arrows preserves identities and composition. -/
theorem projection_laws :
    (∀ ξ : RestrictInclusion X, Hom.base (𝟙 ξ) = 𝟙 ξ.base) ∧
    (∀ (ξ η ζ : RestrictInclusion X) (f : ξ ⟶ η) (g : η ⟶ ζ),
      Hom.base (f ≫ g) = f.base ≫ g.base) :=
  ⟨fun _ ↦ rfl, fun _ _ _ _ _ ↦ rfl⟩

/-- The projection `X|_{C_Λ} ⥤ C_Λ` sending a restricted object to its Artinian base. -/
def projection (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    RestrictInclusion X ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map a := a.base
  map_id := projection_laws.1
  map_comp := projection_laws.2 _ _ _

/-- The projection sends a restricted object to its stored Artinian base. -/
theorem projection_obj (ξ : RestrictInclusion X) :
    (projection X).obj ξ = ξ.base := rfl

/-- The underlying arrows of restrictions preserve identities and composition. -/
theorem ι_laws :
    (∀ ξ : RestrictInclusion X, Hom.obj (𝟙 ξ) = 𝟙 ξ.obj) ∧
    (∀ (ξ η ζ : RestrictInclusion X) (f : ξ ⟶ η) (g : η ⟶ ζ),
      Hom.obj (f ≫ g) = f.obj ≫ g.obj) :=
  ⟨fun _ ↦ rfl, fun _ _ _ _ _ ↦ rfl⟩

/-- Inclusion of the restriction into the total category of `X`. -/
def ι (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    RestrictInclusion X ⥤ X.obj where
  obj ξ := ξ.obj
  map a := a.obj
  map_id := ι_laws.1
  map_comp := ι_laws.2 _ _ _

/-- The inclusion sends a restricted object to its stored object of `X`. -/
theorem ι_obj (ξ : RestrictInclusion X) : (ι X).obj ξ = ξ.obj := rfl

private theorem Hom.op_isHomLift {U V : (ArtinianLocalAlgCat Λ k)ᵒᵖ}
    {ξ η : (RestrictInclusion X)ᵒᵖ} (f : U ⟶ V) (a : ξ ⟶ η)
    [h : (projection X).op.IsHomLift f a] :
    X.p.op.IsHomLift (inclusion.op.map f) a.unop.obj.op := by
  cases h
  change X.p.op.IsHomLift (inclusion.map a.unop.base).op a.unop.obj.op
  have h : X.p.IsHomLift (inclusion.map a.unop.base) a.unop.obj :=
    IsHomLift.of_fac X.p _ _ η.unop.over ξ.unop.over a.unop.over
  exact h.casesOn fun b ↦ IsHomLift.map (p := X.p.op) b.op

private theorem unop_isHomLift {U V : (CompleteLocalAlgCat Λ k)ᵒᵖ}
    {x y : X.objᵒᵖ} {f : U ⟶ V} {a : x ⟶ y} (h : X.p.op.IsHomLift f a) :
    X.p.IsHomLift f.unop a.unop := by
  cases h
  exact IsHomLift.map X.p _

private theorem op_isCartesian [Functor.IsFibered.InGroupoids X.p.op]
    {U V : (ArtinianLocalAlgCat Λ k)ᵒᵖ} {ξ η : (RestrictInclusion X)ᵒᵖ}
    (f : U ⟶ V) (a : ξ ⟶ η) [(projection X).op.IsHomLift f a] :
    (projection X).op.IsCartesian f a := by
  let q := (projection X).op
  have cartesianAt {U V : (CompleteLocalAlgCat Λ k)ᵒᵖ} {x y : X.objᵒᵖ}
      (f : U ⟶ V) (a : x ⟶ y) (h : X.p.op.IsHomLift f a) :
      X.p.op.IsCartesian f a := by
    cases h
    exact Functor.IsFibered.InGroupoids.all_isCartesian a
  letI := cartesianAt _ _ (Hom.op_isHomLift f a)
  have op_ext {ξ η : (RestrictInclusion X)ᵒᵖ} (a b : ξ ⟶ η)
      (hobj : a.unop.obj.op = b.unop.obj.op) (hbase : q.map a = q.map b) : a = b := by
    apply Quiver.Hom.unop_inj
    exact Hom.ext (congrArg Quiver.Hom.unop hobj) (congrArg Quiver.Hom.unop hbase)
  refine { toIsHomLift := inferInstance, universal_property := ?_ }
  intro ζ b hb
  letI := Hom.op_isHomLift f b
  obtain ⟨c, ⟨hc, hfac⟩, huniq⟩ :=
    Functor.IsCartesian.universal_property (p := X.p.op)
      (f := inclusion.op.map f) (φ := a.unop.obj.op) b.unop.obj.op
  letI : X.p.IsHomLift (𝟙 (inclusion.op.obj U)).unop c.unop :=
    unop_isHomLift hc
  let e : ξ.unop.base = ζ.unop.base :=
    congrArg Opposite.unop
      ((IsHomLift.domain_eq q f a).trans (IsHomLift.domain_eq q f b).symm)
  let c' : ζ ⟶ ξ :=
    (show ξ.unop ⟶ ζ.unop from Hom.of c.unop (eqToHom e) (by
      rw [eqToHom_map, IsHomLift.fac' X.p (𝟙 (inclusion.op.obj U)).unop c.unop]
      dsimp only [inclusion]
      simp [Category.assoc])).op
  have hc' : q.IsHomLift (𝟙 U) c' := by
    apply IsHomLift.of_fac q _ _ (IsHomLift.domain_eq q f b) (IsHomLift.domain_eq q f a)
    change (𝟙 U) = eqToHom _ ≫ (eqToHom e).op ≫ eqToHom _
    simp [eqToHom_op, Category.assoc]
  letI := hc'
  refine ⟨c', ⟨hc', ?_⟩, ?_⟩
  · apply op_ext
    · change c ≫ a.unop.obj.op = b.unop.obj.op
      exact hfac
    · exact (IsHomLift.fac' q f (c' ≫ a)).trans (IsHomLift.fac' q f b).symm
  · intro d hd
    letI := hd.1
    apply op_ext
    · have hd' : X.p.op.IsHomLift (𝟙 (inclusion.op.obj U)) d.unop.obj.op := by
        simpa only [Functor.map_id] using (Hom.op_isHomLift (𝟙 U) d)
      have hcomp : d.unop.obj.op ≫ a.unop.obj.op = b.unop.obj.op :=
        congrArg (fun b : ζ ⟶ η ↦ b.unop.obj.op) hd.2
      exact huniq _ ⟨hd', hcomp⟩
    · exact (IsHomLift.fac' q (𝟙 U) d).trans (IsHomLift.fac' q (𝟙 U) c').symm

/-- The restricted projection is cofibered in groupoids. -/
instance projection_op_isFiberedInGroupoids
    (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k))
    [Functor.IsFibered.InGroupoids X.p.op] :
    Functor.IsFibered.InGroupoids (projection X).op where
  exists_isCartesian' := by
    intro ξ U f
    have hξ : X.p.op.obj (Opposite.op ξ.unop.obj) =
        inclusion.op.obj ((projection X).op.obj ξ) := by
      change Opposite.op (X.p.obj ξ.unop.obj) = Opposite.op (toComplete ξ.unop.base)
      exact congrArg Opposite.op ξ.unop.over
    obtain ⟨y, b, hb⟩ := IsPreFibered.exists_isCartesian X.p.op
      (a := Opposite.op ξ.unop.obj) hξ (inclusion.op.map f)
    have hy : X.p.obj y.unop = toComplete U.unop := by
      change X.p.obj y.unop = inclusion.obj U.unop
      exact congrArg Opposite.unop
        (@IsHomLift.domain_eq _ _ _ _ X.p.op _ _ _ _ (inclusion.op.map f) b hb.toIsHomLift)
    let η := of y.unop U.unop hy
    letI : X.p.IsHomLift (inclusion.map f.unop) b.unop :=
      unop_isHomLift hb.toIsHomLift
    let a : Opposite.op η ⟶ ξ :=
      (show ξ.unop ⟶ η from Hom.of b.unop f.unop
        (IsHomLift.fac X.p (inclusion.map f.unop) b.unop)).op
    letI : (projection X).op.IsHomLift f a := IsHomLift.map (projection X).op a
    exact ⟨Opposite.op η, a, op_isCartesian f a⟩
  comp := by
    intro U V W f g ξ η ζ a b ha hb
    letI := ha.toIsHomLift
    letI := hb.toIsHomLift
    letI := IsHomLift.comp (projection X).op f g a b
    exact op_isCartesian (f ≫ g) (a ≫ b)
  all_isCartesian a := op_isCartesian _ a

variable {Y : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}

/-- Applying a based functor preserves the compatibility of a restricted arrow. -/
theorem mapFunctor_over (φ : X ⥤ᵇ Y) {ξ η : RestrictInclusion X} (a : ξ ⟶ η) :
    inclusion.map a.base =
      eqToHom ((BasedFunctor.w_obj φ ξ.obj).trans ξ.over).symm ≫
        Y.p.map (φ.map a.obj) ≫ eqToHom ((BasedFunctor.w_obj φ η.obj).trans η.over) := by
  letI : X.p.IsHomLift (inclusion.map a.base) a.obj :=
    IsHomLift.of_fac X.p _ _ ξ.over η.over a.over
  exact IsHomLift.fac Y.p (inclusion.map a.base) (φ.map a.obj)
private def mapFunctorObj (φ : X ⥤ᵇ Y) (ξ : RestrictInclusion X) : RestrictInclusion Y :=
  of (φ.obj ξ.obj) ξ.base ((BasedFunctor.w_obj φ ξ.obj).trans ξ.over)
private def mapFunctorMap (φ : X ⥤ᵇ Y) {ξ η : RestrictInclusion X} (a : ξ ⟶ η) :
    mapFunctorObj φ ξ ⟶ mapFunctorObj φ η :=
  Hom.of (φ.map a.obj) a.base (mapFunctor_over φ a)
/-- Restriction of a based functor preserves identities and composition. -/
theorem mapFunctor_laws (φ : X ⥤ᵇ Y) :
    (∀ ξ, mapFunctorMap φ (𝟙 ξ) = 𝟙 (mapFunctorObj φ ξ)) ∧
    (∀ (ξ η ζ : RestrictInclusion X) (f : ξ ⟶ η) (g : η ⟶ ζ),
      mapFunctorMap φ (f ≫ g) = mapFunctorMap φ f ≫ mapFunctorMap φ g) := by
  constructor
  · intro ξ
    exact Hom.ext (φ.toFunctor.map_id ξ.obj) rfl
  · intro ξ η ζ f g
    exact Hom.ext (φ.toFunctor.map_comp f.obj g.obj) rfl
/-- Apply a based functor to the underlying objects and arrows of the restriction. -/
def mapFunctor (φ : X ⥤ᵇ Y) : RestrictInclusion X ⥤ RestrictInclusion Y where
  obj := mapFunctorObj φ
  map := mapFunctorMap φ
  map_id := (mapFunctor_laws φ).1
  map_comp := (mapFunctor_laws φ).2 _ _ _

/-- Mapping a restricted object along `φ` preserves the Artinian base. -/
theorem mapFunctor_obj_base (φ : X ⥤ᵇ Y) (ξ : RestrictInclusion X) :
    ((mapFunctor φ).obj ξ).base = ξ.base := rfl

/-- Mapping a restricted object along `φ` applies `φ` to the underlying object. -/
theorem map_obj (φ : X ⥤ᵇ Y) (ξ : RestrictInclusion X) :
    ((mapFunctor φ).obj ξ).obj = φ.obj ξ.obj := rfl

/-- The induced functor commutes with the Artinian projections. -/
theorem map_w (φ : X ⥤ᵇ Y) : mapFunctor φ ⋙ projection Y = projection X := rfl
/-- Restriction of a based functor as a based functor. -/
def map (φ : X ⥤ᵇ Y) :
    BasedCategory.ofFunctor (projection X) ⥤ᵇ BasedCategory.ofFunctor (projection Y) where
  toFunctor := mapFunctor φ
  w := map_w φ

/-- Restriction of a vertical transformation is natural and vertical. -/
theorem map₂_laws {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) :
    (∀ ξ : RestrictInclusion X,
      inclusion.map (𝟙 ξ.base) =
        eqToHom ((mapFunctor φ).obj ξ).over.symm ≫ Y.p.map (t.toNatTrans.app ξ.obj) ≫
          eqToHom ((mapFunctor ψ).obj ξ).over) ∧
    (∀ (h : ∀ ξ : RestrictInclusion X,
      inclusion.map (𝟙 ξ.base) =
        eqToHom ((mapFunctor φ).obj ξ).over.symm ≫ Y.p.map (t.toNatTrans.app ξ.obj) ≫
          eqToHom ((mapFunctor ψ).obj ξ).over),
      (∀ (ξ η : RestrictInclusion X) (a : ξ ⟶ η),
        (mapFunctor φ).map a ≫
          Hom.of (ξ := (mapFunctor φ).obj η) (η := (mapFunctor ψ).obj η)
            (t.toNatTrans.app η.obj) (𝟙 η.base) (h η) =
          Hom.of (ξ := (mapFunctor φ).obj ξ) (η := (mapFunctor ψ).obj ξ)
            (t.toNatTrans.app ξ.obj) (𝟙 ξ.base) (h ξ) ≫ (mapFunctor ψ).map a) ∧
      (∀ ξ : RestrictInclusion X, (projection Y).IsHomLift (𝟙 ξ.base)
        (Hom.of (ξ := (mapFunctor φ).obj ξ) (η := (mapFunctor ψ).obj ξ)
          (t.toNatTrans.app ξ.obj) (𝟙 ξ.base) (h ξ)))) := by
  constructor
  · intro ξ
    letI : Y.p.IsHomLift (𝟙 (toComplete ξ.base)) (t.toNatTrans.app ξ.obj) :=
      BasedNatTrans.isHomLift t ξ.over
    rw [Functor.map_id]
    change (𝟙 (toComplete ξ.base)) = _
    exact IsHomLift.fac Y.p (𝟙 (toComplete ξ.base)) (t.toNatTrans.app ξ.obj)
  · intro h
    constructor
    · intro ξ η a
      exact Hom.ext (t.toNatTrans.naturality a.obj)
        ((Category.comp_id a.base).trans (Category.id_comp a.base).symm)
    · intro ξ
      exact IsHomLift.map (projection Y)
        (Hom.of (ξ := (mapFunctor φ).obj ξ) (η := (mapFunctor ψ).obj ξ)
          (t.toNatTrans.app ξ.obj) (𝟙 ξ.base) (h ξ))
/-- Restriction of a vertical natural transformation. -/
def map₂ {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) : map φ ⟶ map ψ where
  toNatTrans :=
    { app ξ := Hom.of (ξ := (mapFunctor φ).obj ξ) (η := (mapFunctor ψ).obj ξ)
        (t.toNatTrans.app ξ.obj) (𝟙 ξ.base) ((map₂_laws t).1 ξ)
      naturality := fun {ξ η} a ↦ ((map₂_laws t).2 (map₂_laws t).1).1 ξ η a }
  isHomLift' := ((map₂_laws t).2 (map₂_laws t).1).2

/-- The stage-object component of a mapped `2`-cell is the component of `t`. -/
theorem map₂_app (φ ψ : X ⥤ᵇ Y) (t : φ ⟶ ψ) (ξ : RestrictInclusion X) :
    ((map₂ t).toNatTrans.app ξ).obj = t.toNatTrans.app ξ.obj := rfl

end RestrictInclusion

end CategoryTheory.BasedCategory

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

/-- Restriction of a category cofibered in groupoids over `Ĉ_Λ` along
`ArtinianLocalAlgCat.inclusion`, as a category cofibered in groupoids over `C_Λ`. -/
def restrictInclusion
    (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)) :
    CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (ArtinianLocalAlgCat Λ k) :=
  ofFunctor (BasedCategory.RestrictInclusion.projection G.toBasedCategory)

/-- The projection of the bundled restriction is the restricted projection. -/
theorem restrictInclusion_p
    (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)) :
    (restrictInclusion G).p =
      BasedCategory.RestrictInclusion.projection G.toBasedCategory := rfl

end CategoryTheory.CofiberedCategoryOver.Groupoids
