module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.StalkGluing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 32.20.2: let `S` be a scheme, let `s` be a closed point, and suppose the open
complement `U = S \ {s}` is quasi-compact over `S`. Then finitely presented modules on `S` are
equivalent to compatible finitely presented modules on `U` and on `Spec(𝒪_{S,s})`, identified
over the punctured local scheme. -/
@[stacks 0F21] #check
  (AlgebraicGeometry.finitePresentationModules_equivalence_stalkGluing :
    ∀ (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
      (s : S) (_ : s ∈ closedPoints S)
      (_ : (U : Set S) = ({s} : Set S)ᶜ),
      Nonempty
        (FinitePresentationModules S ≌
          finitePresentationModuleGluingCategory U (stalkOpenIntersection S U s)
            ((S.fromSpecStalk s) ∣_ U)))
