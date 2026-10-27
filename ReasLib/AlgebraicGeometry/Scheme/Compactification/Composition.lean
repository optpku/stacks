/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Nagata
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

/-!
# Compactification diagrams for derived étale lower shriek composition

A pair of compatible compactifications `(P_g, P_bar)` for separated finite-type
morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of qcqs schemes, together with the
pullback interior `U` of `Y` in the ambient of `P_bar`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
variable [h_f_separated : IsSeparated X.hom] [h_f_finiteType : Scheme.Hom.FiniteType X.hom]
variable [h_g_separated : IsSeparated g] [h_g_finiteType : Scheme.Hom.FiniteType g]
variable [h_X_compact : CompactSpace X.left] [h_X_quasiSeparated : QuasiSeparatedSpace X.left]
variable [h_Y_compact : CompactSpace Y] [h_Y_quasiSeparated : QuasiSeparatedSpace Y]
variable [h_Z_compact : CompactSpace Z] [h_Z_quasiSeparated : QuasiSeparatedSpace Z]

/-- A compactification of `Y` over `Z` together with a compactification of `X`
over that ambient, as in the construction of `Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!`. -/
structure CompDiagram where
  /-- Compactification of `g : Y ⟶ Z`. -/
  P_g : Of Z (Over.mk g)
  /-- Compactification of `X` over the ambient of `P_g`. -/
  P_bar : Of P_g.obj.right.left (Over.mk (X.hom ≫ Of.ι P_g))

namespace CompDiagram

/-- Package two compatible compactifications as a composition diagram. -/
def of (P_g : Of Z (Over.mk g))
    (P_bar : Of P_g.obj.right.left (Over.mk (X.hom ≫ Of.ι P_g))) :
    CompDiagram X g where
  P_g := P_g
  P_bar := P_bar

variable (C : CompDiagram X g)

/-- The inverse image `U` of `Y` in the ambient of `P_bar`. -/
abbrev interior : Scheme.{u} :=
  pullback (Of.ι C.P_g) C.P_bar.obj.right.hom

/-- The structure map `f' : U ⟶ Y`, base change of the proper ambient map of
`P_bar`. -/
abbrev toBase : interior X g C ⟶ Y :=
  pullback.fst (Of.ι C.P_g) C.P_bar.obj.right.hom

/-- The open immersion `j' : U ⟶ X̄`, base change of the interior of `P_g`. -/
abbrev openImmersion : interior X g C ⟶ C.P_bar.obj.right.left :=
  pullback.snd (Of.ι C.P_g) C.P_bar.obj.right.hom

/-- The compactification triangle of `P_bar` is the pullback commutativity
witness for the map `X ⟶ U`. -/
theorem interior_fac :
    X.hom ≫ Of.ι C.P_g = Of.ι C.P_bar ≫ C.P_bar.obj.right.hom :=
  (Over.w C.P_bar.obj.hom).symm

/-- The interior map `j : X ⟶ U` induced by the compactification of `X` over
`Ȳ`. -/
def ιInterior : X.left ⟶ interior X g C :=
  pullback.lift X.hom (Of.ι C.P_bar) (interior_fac X g C)

/-- The composite ambient morphism `X̄ ⟶ Z`. -/
abbrev toComposite : C.P_bar.obj.right.left ⟶ Z :=
  C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom

/-- The interior immersion of the compactification of `g`. -/
abbrev ιBase : Y ⟶ C.P_g.obj.right.left :=
  Of.ι C.P_g

/-- Unfolding recovers the compactification interior. -/
theorem ιBase_eq : ιBase X g C = Of.ι C.P_g :=
  rfl

/-- The triangle `j ≫ f' = X.hom`. -/
theorem ιInterior_comp_toBase : ιInterior X g C ≫ toBase X g C = X.hom :=
  pullback.lift_fst X.hom (Of.ι C.P_bar) (interior_fac X g C)

/-- The triangle `j ≫ j' = ι P_bar`. -/
theorem ιInterior_comp_openImmersion :
    ιInterior X g C ≫ openImmersion X g C = Of.ι C.P_bar :=
  pullback.lift_snd X.hom (Of.ι C.P_bar) (interior_fac X g C)

/-- The map `f' : U ⟶ Y` is proper, as a base change of the proper ambient map
of `P_bar`. -/
theorem isProper_toBase : IsProper (toBase X g C) :=
  inferInstanceAs (IsProper (pullback.fst (Of.ι C.P_g) C.P_bar.obj.right.hom))

/-- The composite ambient morphism `X̄ ⟶ Z` is proper. -/
theorem isProper_toComposite : IsProper (toComposite X g C) :=
  inferInstanceAs (IsProper (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom))

/-- The induced map `j : X ⟶ U` is an open immersion. -/
theorem isOpenImmersion_ιInterior : IsOpenImmersion (ιInterior X g C) := by
  haveI : IsOpenImmersion (ιInterior X g C ≫ openImmersion X g C) := by
    rw [ιInterior_comp_openImmersion]
    exact C.P_bar.property.isOpenImmersion
  exact IsOpenImmersion.of_comp (ιInterior X g C) (openImmersion X g C)

/-- The induced map `j : X ⟶ U` is quasi-compact. -/
theorem quasiCompact_ιInterior : QuasiCompact (ιInterior X g C) := by
  haveI : IsSeparated (Of.ι C.P_g) := IsSeparated.isSeparated_of_mono _
  haveI : QuasiCompact (ιInterior X g C ≫ openImmersion X g C) := by
    rw [ιInterior_comp_openImmersion]
    exact C.P_bar.property.quasiCompact
  exact QuasiCompact.of_comp (ιInterior X g C) (openImmersion X g C)

/-- The pullback square `U ⟶ X̄` over `Y ⟶ Ȳ`. -/
theorem square_w :
    openImmersion X g C ≫ C.P_bar.obj.right.hom =
      toBase X g C ≫ Of.ι C.P_g :=
  pullback.condition.symm

/-- The open/proper square of a compatible compactification diagram commutes. -/
theorem square :
    CommSq (openImmersion X g C) (toBase X g C) C.P_bar.obj.right.hom
      (Of.ι C.P_g) :=
  ⟨square_w X g C⟩

/-- The interior of `P_bar` is a morphism over `Z` along the composite ambient
map. -/
theorem ι_comp_toComposite :
    Of.ι C.P_bar ≫ toComposite X g C = X.hom ≫ g :=
  (Category.assoc (Of.ι C.P_bar) C.P_bar.obj.right.hom C.P_g.obj.right.hom).symm.trans
    ((congrArg (fun h ↦ h ≫ C.P_g.obj.right.hom) (Over.w C.P_bar.obj.hom)).trans
      ((Category.assoc X.hom (Of.ι C.P_g) C.P_g.obj.right.hom).trans
        (congrArg (fun h ↦ X.hom ≫ h) (Over.w C.P_g.obj.hom))))

/-- The composite interior is a morphism over `Z`. -/
theorem ιInterior_comp_openImmersion_comp_toComposite :
    (ιInterior X g C ≫ openImmersion X g C) ≫ toComposite X g C = X.hom ≫ g :=
  (congrArg (fun h ↦ h ≫ toComposite X g C) (ιInterior_comp_openImmersion X g C)).trans
    (ι_comp_toComposite X g C)

/-- Compactification of `f : X ⟶ Y` with ambient `U` and interior `j`. -/
abbrev ofInterior : Of Y X :=
  ⟨{ left := ⟨PUnit.unit⟩
     right := { left := interior X g C, right := ⟨⟨⟩⟩, hom := toBase X g C }
     hom := Over.homMk (ιInterior X g C) (ιInterior_comp_toBase X g C) },
    { isOpenImmersion := isOpenImmersion_ιInterior X g C
      quasiCompact := quasiCompact_ιInterior X g C
      isProper := isProper_toBase X g C }⟩

/-- Compactification of the composite with the total ambient scheme. -/
abbrev ofComposite : Of Z (Over.mk (X.hom ≫ g)) :=
  ⟨{ left := ⟨PUnit.unit⟩
     right := { left := C.P_bar.obj.right.left, right := ⟨⟨⟩⟩, hom := toComposite X g C }
     hom := Over.homMk (ιInterior X g C ≫ openImmersion X g C)
       (ιInterior_comp_openImmersion_comp_toComposite X g C) },
    { isOpenImmersion := Eq.mpr
        (congrArg (fun j : X.left ⟶ C.P_bar.obj.right.left ↦ IsOpenImmersion j)
          (ιInterior_comp_openImmersion X g C))
        (inferInstanceAs (IsOpenImmersion (Of.ι C.P_bar)))
      quasiCompact := Eq.mpr
        (congrArg (fun j : X.left ⟶ C.P_bar.obj.right.left ↦ QuasiCompact j)
          (ιInterior_comp_openImmersion X g C))
        (inferInstanceAs (QuasiCompact C.P_bar.obj.hom.left))
      isProper := isProper_toComposite X g C }⟩

/-- The interior compactification has the specified ambient object over the base. -/
theorem ofInterior_obj_right :
    (ofInterior X g C).obj.right = Over.mk (toBase X g C) := rfl

/-- The ambient scheme of the interior compactification is the pullback interior. -/
theorem ofInterior_ambient :
    (ofInterior X g C).obj.right.left = interior X g C := rfl

/-- The composite compactification has the specified ambient object over the base. -/
theorem ofComposite_obj_right :
    (ofComposite X g C).obj.right = Over.mk (toComposite X g C) := rfl

/-- The ambient scheme of the composite compactification is the total ambient. -/
theorem ofComposite_ambient :
    (ofComposite X g C).obj.right.left = C.P_bar.obj.right.left := rfl

/-- The interior immersion of `ofInterior` is `j`. -/
theorem ofInterior_ι : Of.ι (ofInterior X g C) = ιInterior X g C :=
  rfl

/-- The structure map of `ofInterior` is `f'`. -/
theorem ofInterior_hom : (ofInterior X g C).obj.right.hom = toBase X g C :=
  rfl

/-- The interior immersion of `ofComposite` is `j' ∘ j`. -/
theorem ofComposite_ι :
    Of.ι (ofComposite X g C) = ιInterior X g C ≫ openImmersion X g C :=
  rfl

/-- The structure map of `ofComposite` is `f̄ ≫ ḡ`. -/
theorem ofComposite_hom :
    (ofComposite X g C).obj.right.hom = toComposite X g C :=
  rfl

/-- The defining diagram satisfies the equalities `j ≫ j' = ι P_bar`, `j ≫ f' = X.hom`, and the
open/proper square commutes. -/
theorem spec :
    ιInterior X g C ≫ openImmersion X g C = Of.ι C.P_bar ∧
      ιInterior X g C ≫ toBase X g C = X.hom ∧
      openImmersion X g C ≫ C.P_bar.obj.right.hom = toBase X g C ≫ Of.ι C.P_g :=
  ⟨ιInterior_comp_openImmersion X g C, ιInterior_comp_toBase X g C,
    square_w X g C⟩

variable {C : CompDiagram X g}

/-- A morphism of composition diagrams is a compatible pair of maps of the
compactifications `P_g` and `P_bar`, inducing maps of `ofInterior` and
`ofComposite`. -/
structure DiagramHom (C D : CompDiagram X g) where
  /-- Map of compactifications of `g : Y ⟶ Z`. -/
  homBase : C.P_g ⟶ D.P_g
  /-- Induced map of compactifications of `f` with ambient the interior `U`. -/
  homInterior : ofInterior X g C ⟶ ofInterior X g D
  /-- Map of compactifications of `g ∘ f` with ambient `P_bar`. -/
  homComposite : ofComposite X g C ⟶ ofComposite X g D
  /-- The ambient map of `P_bar` lies over the ambient map of `P_g`. -/
  homComposite_lieOver :
    Of.ambientMap homComposite ≫ D.P_bar.obj.right.hom =
      C.P_bar.obj.right.hom ≫ Of.ambientMap homBase

  /-- Interior ambient maps commute with the open immersions into the total ambients. -/
  homInterior_openImmersion :
    Of.ambientMap homInterior ≫ openImmersion X g D =
      openImmersion X g C ≫
        (Of.ambientMap homComposite : C.P_bar.obj.right.left ⟶ D.P_bar.obj.right.left)

namespace DiagramHom

variable {C D : CompDiagram X g}

/-- Package compatible maps of `P_g` and `P_bar` as a morphism of composition
diagrams. -/
def of (homBase : C.P_g ⟶ D.P_g)
    (homInterior : ofInterior X g C ⟶ ofInterior X g D)
    (homComposite : ofComposite X g C ⟶ ofComposite X g D)
    (homComposite_lieOver :
      Of.ambientMap homComposite ≫ D.P_bar.obj.right.hom =
        C.P_bar.obj.right.hom ≫ Of.ambientMap homBase)
    (homInterior_openImmersion :
      Of.ambientMap homInterior ≫ openImmersion X g D =
        openImmersion X g C ≫
        (Of.ambientMap homComposite : C.P_bar.obj.right.left ⟶ D.P_bar.obj.right.left)) :
    DiagramHom X g C D where
  homBase := homBase
  homInterior := homInterior
  homComposite := homComposite
  homComposite_lieOver := homComposite_lieOver
  homInterior_openImmersion := homInterior_openImmersion

/-- The scheme map of ambients of `P_bar` underlying `homComposite`. -/
def homBar (φ : DiagramHom X g C D) : C.P_bar.obj.right.left ⟶ D.P_bar.obj.right.left :=
  Of.ambientMap φ.homComposite

/-- Unfolding recovers the ambient map of `homComposite`. -/
theorem homBar_eq (φ : DiagramHom X g C D) :
    homBar X g φ = Of.ambientMap φ.homComposite :=
  rfl

/-- Interior immersions and the `P_bar`/`P_g` triangle of a morphism of
composition diagrams. -/
theorem spec (φ : DiagramHom X g C D) :
    Of.ι (ofInterior X g C) ≫ Of.ambientMap φ.homInterior =
        Of.ι (ofInterior X g D) ∧
      Of.ι C.P_g ≫ Of.ambientMap φ.homBase = Of.ι D.P_g ∧
      Of.ι (ofComposite X g C) ≫ Of.ambientMap φ.homComposite =
        Of.ι (ofComposite X g D) ∧
      Of.ambientMap φ.homComposite ≫ D.P_bar.obj.right.hom =
        C.P_bar.obj.right.hom ≫ Of.ambientMap φ.homBase ∧
      Of.ambientMap φ.homInterior ≫ openImmersion X g D =
        openImmersion X g C ≫
          (Of.ambientMap φ.homComposite : C.P_bar.obj.right.left ⟶ D.P_bar.obj.right.left) := by
  exact ⟨congrArg (fun k ↦ k.left) (Under.w φ.homInterior.hom),
    congrArg (fun k ↦ k.left) (Under.w φ.homBase.hom),
    congrArg (fun k ↦ k.left) (Under.w φ.homComposite.hom),
    φ.homComposite_lieOver, φ.homInterior_openImmersion⟩

/-- A compatible compactification diagram has an identity morphism. -/
def id (C : CompDiagram X g) : DiagramHom X g C C :=
  of X g (𝟙 C.P_g) (𝟙 (ofInterior X g C)) (𝟙 (ofComposite X g C))
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- Composing compatible diagram morphisms preserves compatibility over the base ambient. -/
theorem comp_lieOver {E : CompDiagram X g}
    (φ : DiagramHom X g C D) (ψ : DiagramHom X g D E) :
    Of.ambientMap (φ.homComposite ≫ ψ.homComposite) ≫ E.P_bar.obj.right.hom =
      C.P_bar.obj.right.hom ≫ Of.ambientMap (φ.homBase ≫ ψ.homBase) := by
  change (Of.ambientMap φ.homComposite ≫ Of.ambientMap ψ.homComposite) ≫
    E.P_bar.obj.right.hom =
      C.P_bar.obj.right.hom ≫ (Of.ambientMap φ.homBase ≫ Of.ambientMap ψ.homBase)
  rw [Category.assoc, ψ.homComposite_lieOver, ← Category.assoc,
    φ.homComposite_lieOver, Category.assoc]

/-- Composing compatible diagram morphisms preserves their interior compatibility. -/
theorem comp_interior {E : CompDiagram X g}
    (φ : DiagramHom X g C D) (ψ : DiagramHom X g D E) :
    Of.ambientMap (φ.homInterior ≫ ψ.homInterior) ≫ openImmersion X g E =
      openImmersion X g C ≫
        (Of.ambientMap (φ.homComposite ≫ ψ.homComposite) :
          C.P_bar.obj.right.left ⟶ E.P_bar.obj.right.left) := by
  change (Of.ambientMap φ.homInterior ≫ Of.ambientMap ψ.homInterior) ≫
    openImmersion X g E =
      openImmersion X g C ≫
        ((Of.ambientMap φ.homComposite :
            C.P_bar.obj.right.left ⟶ D.P_bar.obj.right.left) ≫
          (Of.ambientMap ψ.homComposite :
            D.P_bar.obj.right.left ⟶ E.P_bar.obj.right.left))
  rw [Category.assoc, ψ.homInterior_openImmersion, ← Category.assoc,
    φ.homInterior_openImmersion, Category.assoc]

/-- Composition of compatible diagram morphisms composes all three compactification maps. -/
def comp {E : CompDiagram X g} (φ : DiagramHom X g C D) (ψ : DiagramHom X g D E) :
    DiagramHom X g C E :=
  of X g (φ.homBase ≫ ψ.homBase) (φ.homInterior ≫ ψ.homInterior)
    (φ.homComposite ≫ ψ.homComposite) (comp_lieOver X g φ ψ) (comp_interior X g φ ψ)

end DiagramHom

include h_f_separated h_f_finiteType h_g_separated h_g_finiteType
  h_X_compact h_X_quasiSeparated h_Y_compact h_Y_quasiSeparated
  h_Z_compact h_Z_quasiSeparated in
/-- Separated finite-type morphisms of quasi-compact quasi-separated schemes admit compatible
compactification diagrams for composition. -/
theorem nonempty : Nonempty (CompDiagram X g) := sorry

include h_f_separated h_f_finiteType h_g_separated h_g_finiteType
  h_X_compact h_X_quasiSeparated h_Y_compact h_Y_quasiSeparated
  h_Z_compact h_Z_quasiSeparated in
/-- Any two compatible compactification diagrams admit a common compatible refinement. -/
theorem commonRefinement (C D : CompDiagram X g) :
    ∃ E : CompDiagram X g, Nonempty (DiagramHom X g E C) ∧
      Nonempty (DiagramHom X g E D) := sorry

end CompDiagram

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale

end
