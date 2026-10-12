/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Opens of a diagram of topological spaces

The category of opens in a `TopCat`-valued diagram.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w

namespace TopCat

/-- An open subset of one stage of a diagram of topological spaces. -/
def DiagramOpens {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w}) :=
  Σ c : C, Opens (F.obj c)

namespace DiagramOpens

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w})

/-- The stage containing a diagram open. -/
abbrev base (U : DiagramOpens F) : C := U.1

/-- The open subset represented by a diagram open. -/
abbrev opens (U : DiagramOpens F) : Opens (F.obj U.base) := U.2

/-- The diagram open associated to an open of a specified stage. -/
abbrev ofOpens (c : C) (U : Opens (F.obj c)) : DiagramOpens F := ⟨c, U⟩

/-- The stage of `ofOpens F c U` is `c`. -/
@[simp] theorem ofOpens_base (c : C) (U : Opens (F.obj c)) : (ofOpens F c U).base = c := rfl

/-- The open represented by `ofOpens F c U` is `U`. -/
@[simp] theorem ofOpens_opens (c : C) (U : Opens (F.obj c)) : (ofOpens F c U).opens = U := rfl

variable {F}

/-- A morphism of diagram opens consists of a stage map carrying one open into the other. -/
def Hom (U V : DiagramOpens F) :=
  {f : U.base ⟶ V.base // Set.MapsTo (F.map f).hom U.opens V.opens}

/-- The underlying stage map of a morphism of diagram opens. -/
def Hom.base {U V : DiagramOpens F} (f : Hom U V) : U.base ⟶ V.base := f.1

/-- The containment witness of a morphism of diagram opens. -/
def Hom.mapsTo {U V : DiagramOpens F} (f : Hom U V) :
    Set.MapsTo (F.map f.base).hom U.opens V.opens := f.2

/-- Build a morphism of diagram opens from a stage map and a containment witness. -/
def homMk {U V : DiagramOpens F} (base : U.base ⟶ V.base)
    (mapsTo : Set.MapsTo (F.map base).hom U.opens V.opens) : Hom U V := ⟨base, mapsTo⟩

/-- Morphisms of diagram opens are determined by their stage maps. -/
theorem Hom.ext {U V : DiagramOpens F} {f g : Hom U V} (h : f.base = g.base) : f = g := by
  apply Subtype.ext
  exact h

/-- The identity morphism of a diagram open. -/
def Hom.id (U : DiagramOpens F) : Hom U U :=
  ⟨𝟙 U.base, by
    intro x hx
    simpa using hx⟩

/-- Composition of morphisms of diagram opens. -/
def Hom.comp {U V W : DiagramOpens F} (f : Hom U V) (g : Hom V W) : Hom U W :=
  ⟨f.base ≫ g.base, by
    intro x hx
    simpa [Functor.map_comp] using g.mapsTo (f.mapsTo hx)⟩

/-- The stage map of `homMk base mapsTo` is `base`. -/
@[simp] theorem homMk_base {U V : DiagramOpens F} (base : U.base ⟶ V.base)
    (mapsTo : Set.MapsTo (F.map base).hom U.opens V.opens) : (homMk base mapsTo).base = base := rfl

/-- The stage map of an identity morphism is the identity stage map. -/
@[simp] theorem id_base (U : DiagramOpens F) : (Hom.id U).base = 𝟙 U.base := rfl

/-- The stage map of a composite is the composite stage map. -/
@[simp] theorem comp_base {U V W : DiagramOpens F} (f : Hom U V) (g : Hom V W) :
    (Hom.comp f g).base = f.base ≫ g.base := rfl

/-- The inverse image of an open along a diagram-open morphism, restricted to the source. -/
def Hom.preimage {U V : DiagramOpens F} (f : Hom U V) (W : Opens (F.obj V.base)) :
    Opens (F.obj U.base) :=
  (Opens.map (F.map f.base)).obj W ⊓ U.opens

variable (F)

/-- The category of opens of the stages of a topological-space diagram. -/
instance instCategory : Category.{v} (DiagramOpens F) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro U V f
    apply Hom.ext
    simp
  comp_id := by
    intro U V f
    apply Hom.ext
    simp
  assoc := by
    intro U V W Z f g h
    apply Hom.ext
    simp [Category.assoc]

variable {F}

/-- The identity-stage inclusion between nested opens. -/
def homOfLE {c : C} {U V : Opens (F.obj c)} (h : U ≤ V) :
    ofOpens F c U ⟶ ofOpens F c V :=
  homMk (𝟙 c) (by
    intro x hx
    dsimp [base, opens, ofOpens] at x hx ⊢
    change (F.map (𝟙 c)).hom x ∈ V
    rw [F.map_id]
    change x ∈ V
    exact h hx)

variable (F)

/-- The functor embedding the opens of one stage into the diagram-open category. -/
def fiber (c : C) : Opens (F.obj c) ⥤ DiagramOpens F where
  obj U := ofOpens F c U
  map i := homOfLE i.le
  map_id := by
    intro U
    apply Hom.ext
    change (𝟙 c) = 𝟙 c
    rfl
  map_comp := by
    intro U V W i j
    apply Hom.ext
    change (𝟙 c) = (𝟙 c) ≫ 𝟙 c
    simp

/-- The stage inclusion functor sends `U` to `ofOpens F c U`. -/
@[simp] theorem fiber_obj (c : C) (U : Opens (F.obj c)) :
    (fiber F c).obj U = ofOpens F c U := by
  rfl

/-- Every map in a stage inclusion functor has identity stage map. -/
@[simp] theorem fiber_map_base {c : C} {U V : Opens (F.obj c)} (i : U ⟶ V) :
    ((fiber F c).map i).base = 𝟙 c := by
  change (𝟙 c) = 𝟙 c
  rfl

variable {F}

/-- The continuous map induced on the underlying open spaces by a diagram-open morphism. -/
def Hom.toContinuousMap {U V : DiagramOpens F} (f : Hom U V) :
    (Opens.toTopCat (F.obj U.base)).obj U.opens ⟶
      (Opens.toTopCat (F.obj V.base)).obj V.opens :=
  TopCat.ofHom ⟨fun x ↦ ⟨(F.map f.base).hom x.1, f.mapsTo x.2⟩,
    continuous_induced_rng.2 <|
      (F.map f.base).hom.continuous.comp continuous_subtype_val⟩

variable (F)

/-- The functor sending each diagram open to its underlying topological space. -/
def toTopCat : DiagramOpens F ⥤ TopCat.{w} where
  obj U := (Opens.toTopCat (F.obj U.base)).obj U.opens
  map f := Hom.toContinuousMap f
  map_id := by
    intro U
    ext x
    apply Subtype.ext
    dsimp [base, opens] at x ⊢
    change (F.map (𝟙 U.1)).hom x.1 = x.1
    rw [F.map_id]
    rfl
  map_comp := by
    intro U V W f g
    ext x
    apply Subtype.ext
    change (F.map (f.base ≫ g.base)).hom x.1 =
      (F.map g.base).hom ((F.map f.base).hom x.1)
    rw [F.map_comp]
    rfl

/-- The underlying space assigned to a diagram open is its stagewise open subspace. -/
@[simp] theorem toTopCat_obj (U : DiagramOpens F) :
    (toTopCat F).obj U = (Opens.toTopCat (F.obj U.base)).obj U.opens := rfl

end DiagramOpens

end TopCat
