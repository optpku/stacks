/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
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
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsSeparated g] [Scheme.Hom.FiniteType g]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace Z] [QuasiSeparatedSpace Z]

/-- A compactification of `Y` over `Z` together with a compactification of `X`
over that ambient, as in the construction of `Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!`. -/
structure CompDiagram where
  /-- Compactification of `g : Y ⟶ Z`. -/
  P_g : Of Z (Over.mk g)
  /-- Compactification of `X` over the ambient of `P_g`. -/
  P_bar : Of P_g.obj.right.left (Over.mk (X.hom ≫ Of.ι P_g))

namespace CompDiagram

/-- The over-object for `g` has the same underlying morphism as `g`. -/
instance instIsSeparated_overMk_hom : IsSeparated (Over.mk g).hom :=
  inferInstanceAs (IsSeparated g)

/-- Finite type of `g` transfers to `Over.mk g`. -/
instance instFiniteType_overMk_hom : Scheme.Hom.FiniteType (Over.mk g).hom :=
  inferInstanceAs (Scheme.Hom.FiniteType g)

/-- Quasi-compactness of `Y` transfers to the source of `Over.mk g`. -/
instance instCompactSpace_overMk_left : CompactSpace (Over.mk g).left :=
  inferInstanceAs (CompactSpace Y)

/-- Quasi-separatedness of `Y` transfers to the source of `Over.mk g`. -/
instance instQuasiSeparatedSpace_overMk_left :
    QuasiSeparatedSpace (Over.mk g).left :=
  inferInstanceAs (QuasiSeparatedSpace Y)

/-- The over-object for `g ∘ f` has the same underlying morphism as `g ∘ f`. -/
instance instIsSeparated_overMk_compHom :
    IsSeparated (Over.mk (X.hom ≫ g)).hom :=
  inferInstanceAs (IsSeparated (X.hom ≫ g))

/-- Finite type of `g ∘ f` transfers to `Over.mk (X.hom ≫ g)`. -/
instance instFiniteType_overMk_compHom :
    Scheme.Hom.FiniteType (Over.mk (X.hom ≫ g)).hom :=
  inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g))

/-- Quasi-compactness of `X` transfers to the source of `Over.mk (X.hom ≫ g)`. -/
instance instCompactSpace_overMk_comp_left :
    CompactSpace (Over.mk (X.hom ≫ g)).left :=
  inferInstanceAs (CompactSpace X.left)

/-- Quasi-separatedness of `X` transfers to the source of `Over.mk (X.hom ≫ g)`. -/
instance instQuasiSeparatedSpace_overMk_comp_left :
    QuasiSeparatedSpace (Over.mk (X.hom ≫ g)).left :=
  inferInstanceAs (QuasiSeparatedSpace X.left)

/-- Package two compatible compactifications as a composition diagram. -/
def of (P_g : Of Z (Over.mk g))
    (P_bar : Of P_g.obj.right.left (Over.mk (X.hom ≫ Of.ι P_g))) :
    CompDiagram X g where
  P_g := P_g
  P_bar := P_bar

variable (C : CompDiagram X g)

/-- The inverse image `U` of `Y` in the ambient of `P_bar`. -/
def interior : Scheme.{u} :=
  pullback (Of.ι C.P_g) C.P_bar.obj.right.hom

/-- The structure map `f' : U ⟶ Y`, base change of the proper ambient map of
`P_bar`. -/
def toBase : interior X g C ⟶ Y :=
  pullback.fst (Of.ι C.P_g) C.P_bar.obj.right.hom

/-- The open immersion `j' : U ⟶ X̄`, base change of the interior of `P_g`. -/
def openImmersion : interior X g C ⟶ C.P_bar.obj.right.left :=
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
def toComposite : C.P_bar.obj.right.left ⟶ Z :=
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

/-- The interior immersion of the compactification of `g` is an open
immersion. -/
instance instIsOpenImmersion_ιBase : IsOpenImmersion (ιBase X g C) :=
  inferInstanceAs (IsOpenImmersion (Of.ι C.P_g))

/-- The interior immersion of the compactification of `g` is étale. -/
instance instEtale_ιBase : Etale (ιBase X g C) :=
  inferInstance

/-- The interior immersion of the compactification of `g` is separated. -/
instance instIsSeparated_ιBase : IsSeparated (ιBase X g C) :=
  sorry

/-- The interior immersion of the compactification of `g` is locally
quasi-finite. -/
instance instLocallyQuasiFinite_ιBase : LocallyQuasiFinite (ιBase X g C) :=
  sorry

/-- The interior immersion of the compactification of `g` is locally of finite
type. -/
instance instLocallyOfFiniteType_ιBase : LocallyOfFiniteType (ιBase X g C) :=
  sorry

/-- The open immersion `j'` is the second projection of the defining pullback. -/
instance instIsOpenImmersion_openImmersion :
    IsOpenImmersion (openImmersion X g C) :=
  sorry

/-- The map `f' : U ⟶ Y` is proper, as a base change of the proper ambient map
of `P_bar`. -/
instance instIsProper_toBase : IsProper (toBase X g C) :=
  sorry

/-- The composite ambient morphism `X̄ ⟶ Z` is proper. -/
instance instIsProper_toComposite : IsProper (toComposite X g C) :=
  sorry

/-- The composite interior `j' ∘ j` is an open immersion, as the interior of
`P_bar`. -/
instance instIsOpenImmersion_ιInterior_comp_openImmersion :
    IsOpenImmersion (ιInterior X g C ≫ openImmersion X g C) :=
  sorry

/-- The composite interior `j' ∘ j` is quasi-compact, as the interior of
`P_bar`. -/
instance instQuasiCompact_ιInterior_comp_openImmersion :
    QuasiCompact (ιInterior X g C ≫ openImmersion X g C) :=
  sorry

/-- The induced map `j : X ⟶ U` is an open immersion. -/
instance instIsOpenImmersion_ιInterior : IsOpenImmersion (ιInterior X g C) :=
  sorry

/-- The induced map `j : X ⟶ U` is quasi-compact. -/
instance instQuasiCompact_ιInterior : QuasiCompact (ιInterior X g C) :=
  sorry

/-- The induced map `j : X ⟶ U` is locally quasi-finite. -/
instance instLocallyQuasiFinite_ιInterior :
    LocallyQuasiFinite (ιInterior X g C) :=
  sorry

/-- The open immersion `j'` is locally quasi-finite. -/
instance instLocallyQuasiFinite_openImmersion :
    LocallyQuasiFinite (openImmersion X g C) :=
  sorry

/-- The composite interior `j' ∘ j` is locally quasi-finite. -/
instance instLocallyQuasiFinite_ιInterior_comp_openImmersion :
    LocallyQuasiFinite (ιInterior X g C ≫ openImmersion X g C) :=
  sorry

/-- The induced map `j : X ⟶ U` is locally of finite type. -/
instance instLocallyOfFiniteType_ιInterior :
    LocallyOfFiniteType (ιInterior X g C) :=
  sorry

/-- The open immersion `j'` is locally of finite type. -/
instance instLocallyOfFiniteType_openImmersion :
    LocallyOfFiniteType (openImmersion X g C) :=
  sorry

/-- The composite interior `j' ∘ j` is locally of finite type. -/
instance instLocallyOfFiniteType_ιInterior_comp_openImmersion :
    LocallyOfFiniteType (ιInterior X g C ≫ openImmersion X g C) :=
  sorry

/-- The induced map `j : X ⟶ U` is separated. -/
instance instIsSeparated_ιInterior : IsSeparated (ιInterior X g C) :=
  sorry

/-- The open immersion `j'` is separated. -/
instance instIsSeparated_openImmersion : IsSeparated (openImmersion X g C) :=
  sorry

/-- The composite interior `j' ∘ j` is separated. -/
instance instIsSeparated_ιInterior_comp_openImmersion :
    IsSeparated (ιInterior X g C ≫ openImmersion X g C) :=
  sorry

/-- The composite `g ∘ f` is separated. -/
instance instIsSeparated_compHom : IsSeparated (X.hom ≫ g) :=
  inferInstance

/-- The composite `g ∘ f` is of finite type. -/
instance instFiniteType_compHom : Scheme.Hom.FiniteType (X.hom ≫ g) :=
  inferInstance

/-- The pullback square `U ⟶ X̄` over `Y ⟶ Ȳ`. -/
theorem square_w :
    openImmersion X g C ≫ C.P_bar.obj.right.hom =
      toBase X g C ≫ Of.ι C.P_g :=
  pullback.condition.symm

/-- The commutative square used by the Lemma 63.8.1 comparison. -/
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
def ofInterior : Of Y X :=
  @Of.mk Y X (Over.mk (toBase X g C))
    (Over.homMk (ιInterior X g C) (ιInterior_comp_toBase X g C))
    (instIsOpenImmersion_ιInterior X g C)
    (instQuasiCompact_ιInterior X g C)
    (instIsProper_toBase X g C)

/-- Compactification of `g ∘ f : X ⟶ Z` with ambient `X̄` and interior
`j' ∘ j`. -/
def ofComposite : Of Z (Over.mk (X.hom ≫ g)) :=
  @Of.mk Z (Over.mk (X.hom ≫ g)) (Over.mk (toComposite X g C))
    (Over.homMk (ιInterior X g C ≫ openImmersion X g C)
      (ιInterior_comp_openImmersion_comp_toComposite X g C))
    (instIsOpenImmersion_ιInterior_comp_openImmersion X g C)
    (instQuasiCompact_ιInterior_comp_openImmersion X g C)
    (instIsProper_toComposite X g C)

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

/-- Source diagram equalities: `j ≫ j' = ι P_bar`, `j ≫ f' = X.hom`, and the
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

namespace DiagramHom

variable {C D : CompDiagram X g}

/-- Package compatible maps of `P_g` and `P_bar` as a morphism of composition
diagrams. -/
def of (homBase : C.P_g ⟶ D.P_g)
    (homInterior : ofInterior X g C ⟶ ofInterior X g D)
    (homComposite : ofComposite X g C ⟶ ofComposite X g D)
    (homComposite_lieOver :
      Of.ambientMap homComposite ≫ D.P_bar.obj.right.hom =
        C.P_bar.obj.right.hom ≫ Of.ambientMap homBase) :
    DiagramHom X g C D where
  homBase := homBase
  homInterior := homInterior
  homComposite := homComposite
  homComposite_lieOver := homComposite_lieOver

/-- The scheme map of ambients of `P_bar` underlying `homComposite`. -/
def homBar (φ : DiagramHom X g C D) : C.P_bar.obj.right.left ⟶ D.P_bar.obj.right.left :=
  Of.ambientMap φ.homComposite

/-- Unfolding recovers the ambient map of `homComposite`. -/
theorem homBar_eq (φ : DiagramHom X g C D) :
    homBar X g φ = Of.ambientMap φ.homComposite :=
  sorry

/-- Interior immersions and the `P_bar`/`P_g` triangle of a morphism of
composition diagrams. -/
theorem spec (φ : DiagramHom X g C D) :
    Of.ι (ofInterior X g C) ≫ Of.ambientMap φ.homInterior =
        Of.ι (ofInterior X g D) ∧
      Of.ι C.P_g ≫ Of.ambientMap φ.homBase = Of.ι D.P_g ∧
      Of.ι (ofComposite X g C) ≫ Of.ambientMap φ.homComposite =
        Of.ι (ofComposite X g D) ∧
      Of.ambientMap φ.homComposite ≫ D.P_bar.obj.right.hom =
        C.P_bar.obj.right.hom ≫ Of.ambientMap φ.homBase :=
  sorry

end DiagramHom

end CompDiagram

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale

end

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- A morphism of compactifications commutes with the structure maps. -/
theorem ambientMap_comp_structure {S : Scheme.{u}} {X : Over S}
    {P Q : Of S X} (φ : P ⟶ Q) :
    ambientMap φ ≫ Q.obj.right.hom = P.obj.right.hom :=
  Over.w φ.hom.right

/-- A morphism of compactifications is proper, by cancellation of properness
over the base. -/
instance instIsProper_ambientMap {S : Scheme.{u}} {X : Over S}
    {P Q : Of S X} (φ : P ⟶ Q) :
    IsProper (ambientMap φ) :=
  sorry

/-- The interior immersion of a compactification is separated. -/
instance instIsSeparated (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    IsSeparated (ι P) :=
  sorry

/-- The interior immersion of a compactification is locally quasi-finite. -/
instance instLocallyQuasiFinite (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    LocallyQuasiFinite (ι P) :=
  sorry

/-- The interior immersion of a compactification is locally of finite type. -/
instance instLocallyOfFiniteType (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    LocallyOfFiniteType (ι P) :=
  sorry

end AlgebraicGeometry.Scheme.Compactification.Of

end
