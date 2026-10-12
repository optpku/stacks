/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

/-!
# Crystals in quasi-coherent modules on a pre-relation diagram of schemes

A set-theoretic pre-relation diagram of schemes consists of objects `X_i` and morphisms
`f_φ : X_{i'} ⟶ X_i`. A crystal in quasi-coherent modules is a family of quasi-coherent
sheaves `F_i` together with comparison isomorphisms `α_φ : f_φ^* F_i ≅ F_{i'}`, with no
cocycle condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A set-theoretic pre-relation diagram of schemes, with objects indexed by `index` and
morphisms `f_φ : X_{src φ} ⟶ X_{dst φ}` indexed by `arrow`. -/
structure RelDiagram where
  /-- The index set of objects. -/
  index : Type u
  /-- The index set of morphisms. -/
  arrow : Type u
  /-- The source index `i'` of a morphism `f_φ : X_{i'} ⟶ X_i`. -/
  src : arrow → index
  /-- The target index `i` of a morphism `f_φ : X_{i'} ⟶ X_i`. -/
  dst : arrow → index
  /-- The scheme `X_i` at each index. -/
  obj : index → Scheme.{u}
  /-- The morphism `f_φ : X_{src φ} ⟶ X_{dst φ}`. -/
  map (φ : arrow) : obj (src φ) ⟶ obj (dst φ)

namespace RelDiagram

/-- Reconstruct a pre-relation diagram from a map `j : Φ → I × I` with `j φ = (i, i')` and
morphisms `f_φ : X_{i'} ⟶ X_i`. -/
def of {I Φ : Type u} (j : Φ → I × I) (obj : I → Scheme.{u})
    (map : (φ : Φ) → obj (j φ).2 ⟶ obj (j φ).1) : RelDiagram.{u} where
  index := I
  arrow := Φ
  src φ := (j φ).2
  dst φ := (j φ).1
  obj := obj
  map := map

/-- The source index of `of j obj map` is the second component of `j φ`. -/
theorem of_src {I Φ : Type u} (j : Φ → I × I) (obj : I → Scheme.{u})
    (map : (φ : Φ) → obj (j φ).2 ⟶ obj (j φ).1) (φ : Φ) :
    (of j obj map).src φ = (j φ).2 := sorry

/-- The target index of `of j obj map` is the first component of `j φ`. -/
theorem of_dst {I Φ : Type u} (j : Φ → I × I) (obj : I → Scheme.{u})
    (map : (φ : Φ) → obj (j φ).2 ⟶ obj (j φ).1) (φ : Φ) :
    (of j obj map).dst φ = (j φ).1 := sorry

/-- The object family of `of j obj map` is the given family of schemes. -/
theorem of_obj {I Φ : Type u} (j : Φ → I × I) (obj : I → Scheme.{u})
    (map : (φ : Φ) → obj (j φ).2 ⟶ obj (j φ).1) :
    (of j obj map).obj = obj := sorry

/-- The morphism attached to `φ` by `of j obj map` is the given map `f_φ`. -/
theorem of_map {I Φ : Type u} (j : Φ → I × I) (obj : I → Scheme.{u})
    (map : (φ : Φ) → obj (j φ).2 ⟶ obj (j φ).1) (φ : Φ) :
    (of j obj map).map φ = map φ := sorry

/-- A crystal in quasi-coherent modules on a pre-relation diagram of schemes: a quasi-coherent
sheaf on each `X_i` and a comparison isomorphism `α_φ : f_φ^* F_{dst φ} ≅ F_{src φ}`. -/
structure Crystal (X : RelDiagram.{u}) where
  /-- The quasi-coherent sheaf `F_i` on `X_i`. -/
  obj : (i : X.index) → QCoh (X.obj i)
  /-- The comparison isomorphism `α_φ : f_φ^* F_{dst φ} ≅ F_{src φ}`. -/
  iso (φ : X.arrow) :
    (QCoh.pullback (X.map φ)).obj (obj (X.dst φ)) ≅ obj (X.src φ)

namespace Crystal

/-- Reconstruct a crystal from its component sheaves and comparison isomorphisms. -/
def of {X : RelDiagram.{u}} (obj : (i : X.index) → QCoh (X.obj i))
    (iso : (φ : X.arrow) → (QCoh.pullback (X.map φ)).obj (obj (X.dst φ)) ≅ obj (X.src φ)) :
    Crystal X where
  obj := obj
  iso := iso

/-- The object family of `Crystal.of obj iso` is the given family of sheaves. -/
theorem of_obj {X : RelDiagram.{u}} (obj : (i : X.index) → QCoh (X.obj i))
    (iso : (φ : X.arrow) → (QCoh.pullback (X.map φ)).obj (obj (X.dst φ)) ≅ obj (X.src φ)) :
    (of obj iso).obj = obj := sorry

/-- The comparison isomorphism of `Crystal.of obj iso` at `φ` is the given isomorphism. -/
theorem of_iso {X : RelDiagram.{u}} (obj : (i : X.index) → QCoh (X.obj i))
    (iso : (φ : X.arrow) → (QCoh.pullback (X.map φ)).obj (obj (X.dst φ)) ≅ obj (X.src φ))
    (φ : X.arrow) :
    (of obj iso).iso φ = iso φ := sorry

/-- A crystal is `κ`-generated when each component quasi-coherent sheaf is `κ`-generated. -/
def IsKappaGenerated {X : RelDiagram.{u}} (F : Crystal X) (κ : Cardinal.{u}) : Prop :=
  ∀ i : X.index, (F.obj i).obj.IsKappaGenerated κ

/-- `κ`-generation of a crystal is componentwise `κ`-generation of its quasi-coherent sheaves. -/
theorem isKappaGenerated_iff {X : RelDiagram.{u}} (F : Crystal X) (κ : Cardinal.{u}) :
    F.IsKappaGenerated κ ↔ ∀ i : X.index, (F.obj i).obj.IsKappaGenerated κ := sorry

/-- A morphism of crystals is a family of quasi-coherent morphisms compatible with the
comparison isomorphisms. -/
structure Hom {X : RelDiagram.{u}} (F G : Crystal X) where
  /-- The underlying family of quasi-coherent morphisms. -/
  hom : (i : X.index) → F.obj i ⟶ G.obj i
  /-- Compatibility of the family with the comparison isomorphisms `α_φ`. -/
  compatibility (φ : X.arrow) :
    CommSq ((QCoh.pullback (X.map φ)).map (hom (X.dst φ)))
      (F.iso φ).hom (G.iso φ).hom (hom (X.src φ))

namespace Hom

/-- Reconstruct a crystal morphism from a compatible family of quasi-coherent morphisms. -/
def of {X : RelDiagram.{u}} {F G : Crystal X} (hom : (i : X.index) → F.obj i ⟶ G.obj i)
    (compatibility : ∀ φ : X.arrow,
      CommSq ((QCoh.pullback (X.map φ)).map (hom (X.dst φ)))
        (F.iso φ).hom (G.iso φ).hom (hom (X.src φ))) : Hom F G where
  hom := hom
  compatibility := compatibility

/-- Crystal morphisms are determined by their underlying families of module morphisms. -/
theorem ext {X : RelDiagram.{u}} {F G : Crystal X} {f g : Hom F G} (h : f.hom = g.hom) :
    f = g := sorry

/-- The identity crystal morphism. -/
def id {X : RelDiagram.{u}} (F : Crystal X) : Hom F F where
  hom := fun _ ↦ 𝟙 _
  compatibility := sorry

/-- The underlying family of the identity crystal morphism is componentwise the identity. -/
theorem id_hom {X : RelDiagram.{u}} (F : Crystal X) (i : X.index) :
    (id F).hom i = 𝟙 (F.obj i) := sorry

/-- Composition of crystal morphisms. -/
def comp {X : RelDiagram.{u}} {F G H : Crystal X} (f : Hom F G) (g : Hom G H) : Hom F H where
  hom := fun i ↦ f.hom i ≫ g.hom i
  compatibility := sorry

/-- The underlying family of a composite crystal morphism is the componentwise composite. -/
theorem comp_hom {X : RelDiagram.{u}} {F G H : Crystal X} (f : Hom F G) (g : Hom G H)
    (i : X.index) :
    (comp f g).hom i = f.hom i ≫ g.hom i := sorry

end Hom

end Crystal

/-- The category of crystals in quasi-coherent modules on `X`, in the source notation `CQC(X)`. -/
abbrev CQC (X : RelDiagram.{u}) := Crystal X

/-- Source notation `CQC(X)` is the type of crystals on the diagram `X`. -/
theorem CQC_eq (X : RelDiagram.{u}) : CQC X = Crystal X := sorry

end RelDiagram

end AlgebraicGeometry.Scheme
