module

public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.19.3: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space. Let `U, V ⊂ X` be quasi-compact open subspaces. Let `b : V' ⟶ V` be a
`(U ∩ V)`-admissible blowup. Then there exists a `U`-admissible blowup `X' ⟶ X` whose
restriction to `V` is `V'`. -/
@[stacks 086D] #check
  (exists_isAdmissibleBlowup_restrict_iso_of_isAdmissibleBlowup_inter :
    ∀ {S : Scheme.{u}} {X V' : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (U V : OpenSubspace X)
      [QuasiCompact U.ι] [QuasiCompact V.ι] (b : V' ⟶ V.X),
      IsAdmissibleBlowup (U.preimage V) b →
        ∃ (X' : AlgebraicSpace S) (π : X' ⟶ X),
          IsAdmissibleBlowup U π ∧
            Nonempty (Over.mk (pullback.snd π V.ι) ≅ Over.mk b))
