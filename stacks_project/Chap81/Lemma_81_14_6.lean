/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup

/-!
# Lemma 81.14.6

An étale morphism into a finite-type separated algebraic space over a qcqs
base extends to a proper morphism after an admissible blowup of a
compactification.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.14.6. Let `S` be a scheme. Let `B` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `U` be an algebraic space of
finite type and separated over `B`. Let `h : V ⟶ U` be an étale morphism.
If `V` has a compactification `ι : V ⟶ Y` over `B`, then there exists a
`V`-admissible blowing up `b : Y' ⟶ Y` and an open `V ⊂ V' ⊂ Y'` such that
`h` extends to a proper morphism `g : V'.X ⟶ U`. -/
@[stacks 0F4A]
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
