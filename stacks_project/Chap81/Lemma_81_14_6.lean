module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Compactification.ProperExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 81.14.6. Let `S` be a scheme. Let `B` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `U` be an algebraic space of
finite type and separated over `B`. Let `h : V ⟶ U` be an étale morphism.
If `V` has a compactification `ι : V ⟶ Y` over `B`, then there exists a
`V`-admissible blowing up `b : Y' ⟶ Y` and an open `V ⊂ V' ⊂ Y'` such that
`h` extends to a proper morphism `g : V'.X ⟶ U`. -/
@[stacks 0F4A] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_properExtension :
    ∀ {S : Scheme.{u}} {B U V Y : AlgebraicSpace S}
      [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
      (f : U ⟶ B) [FiniteType f] [Separated f]
      (h : V ⟶ U) [Etale h]
      (ι : V ⟶ Y) [IsOpenImmersion ι] [QuasiCompact ι]
      (p : Y ⟶ B) [Proper p] (h_over : ι ≫ p = h ≫ f),
      ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y),
        IsAdmissibleBlowup (OpenSubspace.ofι ι) b ∧
          ∃ (V' : OpenSubspace Y') (j : V ⟶ V'.X) (g : V'.X ⟶ U),
            IsOpenImmersion j ∧ j ≫ V'.ι ≫ b = ι ∧ Proper g ∧ j ≫ g = h)

end AlgebraicGeometry.AlgebraicSpace
