/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.PUnit
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Costructured arrows and bicategorical slices

This leaf specializes colax and pseudo comma bicategories to a terminal right
leg, and owns the normalized constructors and computation API used by downstream
cone and slice constructions.
-/

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

section CostructuredArrowImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The colax costructured-arrow bicategory from `K : A ⥤ᵖ C` to `X : C`.

It is the specialization of `ColaxComma` in which the right pseudofunctor is the
terminal-point pseudofunctor selecting `X`. -/
@[stacks 003Q "colax costructured-arrow bicategory"]
def ColaxCostructuredArrow (K : A ⥤ᵖ C) (X : C) :=
  ColaxComma K (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X)

namespace ColaxCostructuredArrow

variable {K : A ⥤ᵖ C} {X : C}

/-- The bicategory structure inherited by the terminal-right-leg colax comma specialization. -/
instance bicategory : Bicategory (ColaxCostructuredArrow K X) :=
  inferInstanceAs (Bicategory (ColaxComma K (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X)))

/-- A colax costructured-arrow bicategory is locally groupoidal when its source bicategory is;
the terminal endpoint contributes no additional noninvertible `2`-morphisms. -/
instance locallyGroupoid [IsLocallyGroupoid A] :
    IsLocallyGroupoid (ColaxCostructuredArrow K X) :=
  inferInstanceAs
    (IsLocallyGroupoid (ColaxComma K (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X)))

namespace Implementation

/-- The canonical object of the terminal bicategory used by a costructured arrow. -/
private def point : LocallyDiscrete (Discrete PUnit.{1}) :=
  ⟨⟨PUnit.unit⟩⟩

/-- The unique `1`-morphism between two objects of the terminal bicategory. -/
private def pointMap (S T : ColaxCostructuredArrow K X) : S.right ⟶ T.right :=
  (Discrete.eqToHom (Subsingleton.elim S.right.as.as T.right.as.as)).toLoc

end Implementation

/-- Construct a colax costructured arrow from its source and structural map. -/
def mk (left : A) (hom : K.obj left ⟶ X) : ColaxCostructuredArrow K X where
  left := left
  right := Implementation.point
  hom := hom

/-- The source object of a colax costructured arrow. -/
abbrev left (S : ColaxCostructuredArrow K X) : A :=
  ColaxComma.left S

/-- The structural map of a colax costructured arrow. -/
abbrev hom (S : ColaxCostructuredArrow K X) : K.obj S.left ⟶ X :=
  ColaxComma.hom S

/-- The comparison functor represented by a colax costructured arrow. -/
def comparison (T : ColaxCostructuredArrow K X) (a : A) :
    (a ⟶ T.left) ⥤ (K.obj a ⟶ X) :=
  K.mapFunctor a T.left ⋙ postcomp (K.obj a) T.hom

/-- A colax costructured arrow is universal when each represented comparison
functor is an equivalence of categories.

This is the shape-independent bicategorical universal property underlying
conical bilimits, pseudo-pullbacks, and other specialized costructured-arrow
presentations. -/
@[stacks 003Q "represented universal costructured arrow"]
class IsUniversal (T : ColaxCostructuredArrow K X) : Prop where
  /-- Every represented comparison functor is an equivalence. -/
  comparison_isEquivalence (a : A) : (T.comparison a).IsEquivalence

attribute [instance] IsUniversal.comparison_isEquivalence

/-- The source map of a colax costructured-arrow `1`-morphism. -/
abbrev map {S T : ColaxCostructuredArrow K X} (f : S ⟶ T) :
    S.left ⟶ T.left :=
  f.left

/-- The normalized comparison cell of a colax costructured-arrow `1`-morphism. -/
def fac {S T : ColaxCostructuredArrow K X} (f : S ⟶ T) :
    K.map (map f) ≫ T.hom ⟶ S.hom :=
  f.cell ≫ (ρ_ S.hom).hom

/-- Construct a colax costructured-arrow `1`-morphism from a source map and a
comparison cell. -/
def homMk {S T : ColaxCostructuredArrow K X} (map : S.left ⟶ T.left)
    (fac : K.map map ≫ T.hom ⟶ S.hom) : S ⟶ T where
  left := map
  right := Implementation.pointMap S T
  cell := fac ≫ (ρ_ S.hom).inv

/-- The `1`-morphism constructor exposes its source map. -/
@[simp]
theorem homMk_map {S T : ColaxCostructuredArrow K X}
    (map : S.left ⟶ T.left) (fac : K.map map ≫ T.hom ⟶ S.hom) :
    ColaxCostructuredArrow.map (homMk map fac) = map := sorry
/- Proof strategy: unfold `map` and `homMk`; the left comma component is definitionally `map`. -/

/-- The normalized comparison of a constructed `1`-morphism is the supplied comparison cell. -/
@[simp]
theorem homMk_fac {S T : ColaxCostructuredArrow K X}
    (map : S.left ⟶ T.left) (fac : K.map map ≫ T.hom ⟶ S.hom) :
    ColaxCostructuredArrow.fac (homMk map fac) = fac := sorry
/- Proof strategy: unfold `fac` and `homMk`, reassociate, and cancel the inserted inverse right
unitor with its forward right unitor. -/

/-- Costructured-arrow `1`-morphisms are determined by their source map and normalized
comparison cell. -/
@[ext (iff := false)]
theorem hom_ext {S T : ColaxCostructuredArrow K X} (f g : S ⟶ T)
    (hmap : map f = map g)
    (hfac : (T.comparison S.left).map (eqToHom hmap) ≫ fac g = fac f) :
    f = g := sorry
/- Proof strategy: convert the functorial transport in `hfac` to equality transport, then apply
ambient comma hom extensionality; the terminal right endpoint is unique. -/

/-- Reconstructing a costructured-arrow morphism from its normalized projections is identity. -/
@[simp]
theorem homMk_map_fac {S T : ColaxCostructuredArrow K X} (f : S ⟶ T) :
    homMk (map f) (fac f) = f := sorry
/- Proof strategy: apply `hom_ext`; the map projection is reflexive and the comparison projection
reduces using `homMk_fac`. -/

/-- The source `2`-morphism underlying a colax costructured-arrow `2`-morphism. -/
abbrev map₂ {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (η : f ⟶ g) : map f ⟶ map g :=
  η.left

/-- Every costructured-arrow `2`-morphism satisfies the normalized comparison equation. -/
theorem map₂_fac {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T} (η : f ⟶ g) :
    (T.comparison S.left).map (map₂ η) ≫ fac g = fac f := sorry
/- Proof strategy: start from the ambient comma compatibility equation, use terminal discreteness
on the right endpoint, and cancel the right unitors used to define `fac`. -/

namespace Implementation

/-- The unique terminal-endpoint `2`-morphism between the right components of two
costructured-arrow morphisms. -/
private def terminalMap₂ {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T} :
    f.right ⟶ g.right :=
  Discrete.eqToHom (Subsingleton.elim f.right.as g.right.as)

/-- Raw comma compatibility induced by a normalized costructured-arrow compatibility equation. -/
private theorem hom₂Mk_w {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (η : map f ⟶ map g)
    (comm : (T.comparison S.left).map η ≫ fac g = fac f) :
    (K.map₂ η ▷ T.hom) ≫ g.cell =
      f.cell ≫ (S.hom ◁ (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X).map₂
        (terminalMap₂ (f := f) (g := g))) := sorry
/- Proof strategy: unfold `comparison` and both normalized comparison cells, cancel the right
unitors, and use `Pseudofunctor.const.map₂` to reduce the terminal endpoint cell to an identity. -/

end Implementation

/-- Construct a costructured-arrow `2`-morphism from a source cell satisfying the normalized
comparison equation. -/
def hom₂Mk {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (η : map f ⟶ map g)
    (comm : (T.comparison S.left).map η ≫ fac g = fac f) : f ⟶ g :=
  ColaxComma.hom₂Mk η
    (Implementation.terminalMap₂ (f := f) (g := g))
    (Implementation.hom₂Mk_w η comm)

/-- The `2`-morphism constructor exposes its source cell. -/
@[simp]
theorem hom₂Mk_map₂ {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (η : map f ⟶ map g)
    (comm : (T.comparison S.left).map η ≫ fac g = fac f) :
    map₂ (hom₂Mk η comm) = η := sorry
/- Proof strategy: unfold `map₂` and `hom₂Mk`; the left comma component is definitionally `η`. -/

/-- Costructured-arrow `2`-morphisms are determined by their source cells. -/
@[ext]
theorem hom₂_ext {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T} {η θ : f ⟶ g}
    (h : map₂ η = map₂ θ) : η = θ := sorry
/- Proof strategy: apply ambient comma `Hom₂.ext`; use `h` on the left component and
subsingleton elimination in the terminal right hom-category. -/

/-- Reconstructing a costructured-arrow `2`-morphism from its source cell is identity. -/
@[simp]
theorem hom₂Mk_map₂_fac {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (η : f ⟶ g) : hom₂Mk (map₂ η) (map₂_fac η) = η := sorry
/- Proof strategy: apply `hom₂_ext` and simplify the source-cell projection with
`hom₂Mk_map₂`. -/

/- Data audit (mathlib 4.32): the generic `Pseudofunctor.const` owns explicit object,
`1`-morphism, and `2`-morphism data; its `sorryAx` is confined to coherence fields. The objects,
endpoint maps, and source cells of `mk`, `homMk`, and `hom₂Mk` are explicit. Their inherited
axiom report mentions only pseudofunctor coherence and the proof-valued compatibility field of
`hom₂Mk`; no carrier or morphism datum is selected by a `sorry` witness. -/

end ColaxCostructuredArrow

/-- The colax slice bicategory over `X`. -/
def ColaxSlice (X : B) :=
  ColaxCostructuredArrow (Pseudofunctor.id B) X

/-- The bicategory structure on the colax slice specialization. -/
instance colaxSliceBicategory (X : B) : Bicategory (ColaxSlice X) :=
  inferInstanceAs (Bicategory
    (ColaxCostructuredArrow (Pseudofunctor.id B) X))

/-- The pseudo costructured-arrow bicategory from `K : A ⥤ᵖ C` to `X : C`.

It is the terminal-right-leg specialization of the generic pseudo comma
bicategory. -/
@[stacks 003Q "pseudo costructured-arrow bicategory"]
def PseudoCostructuredArrow (K : A ⥤ᵖ C) (X : C) :=
  PseudoComma K (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X)

namespace PseudoCostructuredArrow

variable {K : A ⥤ᵖ C} {X : C}

/-- The bicategory structure inherited by the terminal-right-leg pseudo comma specialization. -/
instance bicategory : Bicategory (PseudoCostructuredArrow K X) :=
  inferInstanceAs (Bicategory (PseudoComma K (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X)))

/-- A pseudo costructured-arrow bicategory is locally groupoidal when its source bicategory is. -/
instance locallyGroupoid [IsLocallyGroupoid A] :
    IsLocallyGroupoid (PseudoCostructuredArrow K X) :=
  inferInstanceAs
    (IsLocallyGroupoid (PseudoComma K (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X)))

/-- Construct a pseudo costructured arrow from its source and structural map. -/
def mk (left : A) (hom : K.obj left ⟶ X) : PseudoCostructuredArrow K X :=
  ColaxCostructuredArrow.mk left hom

/-- The source object of a pseudo costructured arrow. -/
abbrev left (S : PseudoCostructuredArrow K X) : A :=
  ColaxComma.left S

/-- The structural map of a pseudo costructured arrow. -/
abbrev hom (S : PseudoCostructuredArrow K X) : K.obj S.left ⟶ X :=
  ColaxComma.hom S

/-- The comparison functor represented by a pseudo costructured arrow. -/
def comparison (T : PseudoCostructuredArrow K X) (a : A) :
    (a ⟶ T.left) ⥤ (K.obj a ⟶ X) :=
  K.mapFunctor a T.left ⋙ postcomp (K.obj a) T.hom

/-- The source map of a pseudo costructured-arrow `1`-morphism. -/
abbrev map {S T : PseudoCostructuredArrow K X} (f : S ⟶ T) :
    S.left ⟶ T.left :=
  PseudoComma.left f

/-- The normalized comparison cell of a pseudo costructured-arrow `1`-morphism. -/
def fac {S T : PseudoCostructuredArrow K X} (f : S ⟶ T) :
    K.map (map f) ≫ T.hom ⟶ S.hom :=
  PseudoComma.cell f ≫ (ρ_ S.hom).hom

/-- The normalized comparison cell is invertible because both its raw comma
comparison and the right unitor are invertible. -/
theorem fac_isIso {S T : PseudoCostructuredArrow K X} (f : S ⟶ T) :
    IsIso (fac f) := sorry
/- Proof strategy: unfold `fac`; its first factor is the selected invertible pseudo-comma
comparison and its second is a right unitor, so the composite is invertible. -/

/-- The normalized comparison cell of a pseudo costructured-arrow morphism is invertible. -/
instance facIsIso {S T : PseudoCostructuredArrow K X} (f : S ⟶ T) :
    IsIso (fac f) :=
  fac_isIso f

/-- The normalized comparison carried by a pseudo costructured-arrow morphism. -/
noncomputable def facIso {S T : PseudoCostructuredArrow K X} (f : S ⟶ T) :
    K.map (map f) ≫ T.hom ≅ S.hom :=
  asIso (fac f)

/-- Construct a pseudo costructured-arrow `1`-morphism from a source map and an
invertible comparison. -/
def homMk {S T : PseudoCostructuredArrow K X} (map : S.left ⟶ T.left)
    (fac : K.map map ≫ T.hom ≅ S.hom) : S ⟶ T :=
  PseudoComma.homMk map (ColaxCostructuredArrow.Implementation.pointMap S T)
     (fac ≪≫ (ρ_ S.hom).symm)

/-- The source `2`-morphism underlying a pseudo costructured-arrow `2`-morphism. -/
abbrev map₂ {S T : PseudoCostructuredArrow K X} {f g : S ⟶ T}
    (η : f ⟶ g) : map f ⟶ map g :=
  PseudoComma.left₂ η

variable (K X) in
/-- The canonical inclusion from pseudo to colax costructured arrows.

The defining pseudofunctor and target object are explicit because this canonical
pseudofunctor has no value input from which to infer them. -/
def ι : StrictPseudofunctor
    (PseudoCostructuredArrow K X) (ColaxCostructuredArrow K X) :=
  PseudoComma.ι K
    (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X)

end PseudoCostructuredArrow

/-- The pseudo slice bicategory over `X`. -/
def PseudoSlice (X : B) :=
  PseudoCostructuredArrow (Pseudofunctor.id B) X

/-- The bicategory structure on the pseudo slice specialization. -/
instance pseudoSliceBicategory (X : B) : Bicategory (PseudoSlice X) :=
  inferInstanceAs (Bicategory
    (PseudoCostructuredArrow (Pseudofunctor.id B) X))

end CostructuredArrowImplementation

end Bicategory

end CategoryTheory
