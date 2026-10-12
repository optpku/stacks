/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.Open
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology

/- Lemma 52.28.2: For a proper scheme `X` over a field, an ample invertible module `L`,
a section `s`, a coherent module `F`, and an open subscheme `V` containing `Z(s)`,
the restriction map from sections on `V` to the inverse limit of sections on the
infinitesimal neighbourhoods `Z(sⁿ)` is an isomorphism under the stated depth condition. -/
@[stacks 0EL2] #check
  (AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.openComparison_isIso_of_depth :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (V : P.left.Opens)
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (F : P.left.Modules) [F.IsCoherent]
    (h_contains : Set.range (Scheme.zeroSchemeι L s) ⊆ (V : Set P.left))
    (hdepth : ∀ p : P.left, p ∉ Set.range (Scheme.zeroSchemeι L s) →
        ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P p)
        (RingedSpace.stalkModuleCat F p)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({p} : Set P.left))) > (1 : EInt)),
    IsIso (openComparison P V L s F))

end AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology
