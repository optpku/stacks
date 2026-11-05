/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Associativity
import StacksCheckRecall

/-!
# Associativity of derived étale lower shriek composition

Lemma 63.9.3: for separated finite-type morphisms of quasi-compact
quasi-separated schemes, the Lemma 63.9.2 composition identifications form a
commutative square `Rh_! ∘ Rg_! ∘ Rf_! ⇉ R(h ∘ g ∘ f)_!`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

universe u v

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [hf_sep : IsSeparated X.hom] [hf_ft : Hom.FiniteType X.hom]
  [hg_sep : IsSeparated g] [hg_ft : Hom.FiniteType g]
  [hh_sep : IsSeparated h] [hh_ft : Hom.FiniteType h]
  [hXc : CompactSpace X.left] [hXqs : QuasiSeparatedSpace X.left]
  [hYc : CompactSpace Y] [hYqs : QuasiSeparatedSpace Y]
  [hZc : CompactSpace Z] [hZqs : QuasiSeparatedSpace Z]
  [hTc : CompactSpace T] [hTqs : QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/- Lemma 63.9.3: the canonical composition square commutes for separated
finite-type morphisms between quasi-compact, quasi-separated schemes.
The remaining arguments of each route are the coefficient ring and the
original technical instances, retained as the domain of this family equality.
Specializing the equality gives `comp_assoc` and `comp_assoc_app`; no new
localization or comparison data are chosen by the chapter. -/
@[stacks 0F7K] #check
  (congrArg (fun route => @route Y Z T X g h hf_sep hf_ft hg_sep hg_ft hh_sep hh_ft
      hXc hXqs hYc hYqs hZc hZqs hTc hTqs A)
    comp_assoc_function.{u, v} :
    @CanonicalAssociativity.leftPath.{u, v} Y Z T X g h
      hf_sep hf_ft hg_sep hg_ft hh_sep hh_ft hXc hXqs hYc hYqs hZc hZqs hTc hTqs A =
    @CanonicalAssociativity.rightPath.{u, v} Y Z T X g h
      hf_sep hf_ft hg_sep hg_ft hh_sep hh_ft hXc hXqs hYc hYqs hZc hZqs hTc hTqs A)

end
