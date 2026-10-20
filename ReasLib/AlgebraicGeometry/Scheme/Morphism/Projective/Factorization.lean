/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Constructors
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.SchemeTheoreticImage

/-!
# Factorizations of projective scheme morphisms

This file gives factorizations of scheme morphisms through projective morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An H-quasi-projective morphism factors as an open immersion followed by an
H-projective morphism. -/
theorem HQuasiProjective.exists_factor_openImmersion_hProjective
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : HQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S)
      (_ : IsOpenImmersion i) (_ : HProjective g),
        i ≫ g = f := sorry

/-- A quasi-projective morphism over a quasi-compact, quasi-separated base factors as an open
immersion followed by a projective morphism. -/
theorem QuasiProjective.exists_factor_openImmersion_projective
    {X S : Scheme.{u}} {f : X ⟶ S} [CompactSpace S] [QuasiSeparatedSpace S]
    (hf : QuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S)
      (_ : IsOpenImmersion i) (_ : Projective g),
        i ≫ g = f := sorry

end AlgebraicGeometry
