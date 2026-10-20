/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale morphism into a separated finite-type algebraic space over a quasi-compact,
quasi-separated base extends properly to an open neighborhood after an admissible blowup
of its chosen compactification. -/
theorem exists_isAdmissibleBlowup_properExtension
    {S : Scheme.{u}} {B U V Y : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : U ⟶ B) [FiniteType f] [Separated f]
    (h : V ⟶ U) [Etale h]
    (ι : V ⟶ Y) [IsOpenImmersion ι] [QuasiCompact ι]
    (p : Y ⟶ B) [Proper p] (h_over : ι ≫ p = h ≫ f) :
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y),
      IsAdmissibleBlowup (OpenSubspace.ofι ι) b ∧
        ∃ (V' : OpenSubspace Y') (j : V ⟶ V'.X) (g : V'.X ⟶ U),
          IsOpenImmersion j ∧ j ≫ V'.ι ≫ b = ι ∧ Proper g ∧ j ≫ g = h :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
