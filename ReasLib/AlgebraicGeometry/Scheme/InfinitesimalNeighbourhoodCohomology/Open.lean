module

public import ReasLib.AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback
public import Mathlib.Order.WithBotTop

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology

/-- The degree-zero infinitesimal-neighbourhood system after restricting `L`, `s`, and `F`
to the open subscheme `V`. -/
noncomputable def openSystem
    {k : Type u} [Field k] (P : SchemeOverField k) (V : P.left.Opens)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) : SequentialInverseSystem (ModuleCat k) :=
  @system k _ (Over.mk (V.ι ≫ P.hom))
    ((Scheme.Modules.pullback V.ι).obj L) (Scheme.Modules.pullback_isInvertible V.ι L)
    (Scheme.Modules.sectionsPullback V.ι L s) ((Scheme.Modules.pullback V.ι).obj F) 0

/-- The restricted and ambient infinitesimal-neighbourhood systems are isomorphic when `V`
contains the zero scheme of `s`. -/
theorem openSystem_isomorphic
    {k : Type u} [Field k] (P : SchemeOverField k) (V : P.left.Opens)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules)
    (h_contains : Set.range (Scheme.zeroSchemeι L s) ⊆ (V : Set P.left)) :
    IsIsomorphic (openSystem P V L s F) (system P L s F 0) := sorry

/-- The concrete degree-zero comparison from sections on `V` to the limit of the restricted
infinitesimal-neighbourhood system. -/
noncomputable def openComparison
    {k : Type u} [Field k] (P : SchemeOverField k) (V : P.left.Opens)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) :
    Scheme.Hom.cohomology (V.ι ≫ P.hom)
      ((Scheme.Modules.pullback V.ι).obj F) 0 ⟶
      limit (openSystem P V L s F) :=
  @comparison k _ (Over.mk (V.ι ≫ P.hom))
    ((Scheme.Modules.pullback V.ι).obj L) (Scheme.Modules.pullback_isInvertible V.ι L)
    (Scheme.Modules.sectionsPullback V.ι L s) ((Scheme.Modules.pullback V.ι).obj F) 0

/-- Each projection of `openComparison` is the canonical restriction to the corresponding
positive infinitesimal neighbourhood of the restricted section. -/
theorem openComparison_π
    {k : Type u} [Field k] (P : SchemeOverField k) (V : P.left.Opens)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (n : ℕ) :
    openComparison P V L s F ≫ limit.π (openSystem P V L s F) (op n) =
      @restriction k _ (Over.mk (V.ι ≫ P.hom))
        ((Scheme.Modules.pullback V.ι).obj L) (Scheme.Modules.pullback_isInvertible V.ι L)
        (Scheme.Modules.sectionsPullback V.ι L s) ((Scheme.Modules.pullback V.ι).obj F) 0 n := sorry

/-- For a proper scheme over a field, an ample invertible module `L` with section `s`, and
a coherent module `F`, sections on any open subscheme containing `Z(s)` map isomorphically
to the inverse limit over the positive infinitesimal neighbourhoods of `Z(s)` when
`depth(Fₚ) + dim(closure {p}) > 1` away from `Z(s)`. -/
theorem openComparison_isIso_of_depth
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (V : P.left.Opens)
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (F : P.left.Modules) [F.IsCoherent]
    (h_contains : Set.range (Scheme.zeroSchemeι L s) ⊆ (V : Set P.left))
    (hdepth : ∀ p : P.left, p ∉ Set.range (Scheme.zeroSchemeι L s) →
        ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P p)
        (RingedSpace.stalkModuleCat F p)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({p} : Set P.left))) > (1 : EInt)) :
    IsIso (openComparison P V L s F) := sorry

/-- Under the depth-plus-closure-dimension bound away from `Z(s)`, the degree-zero comparison
from an open neighbourhood of `Z(s)` remains an isomorphism after transport along any explicit
isomorphism from its restricted infinitesimal-neighbourhood system to the ambient system. -/
theorem openComparison_toAmbient_isIso_of_depth
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (V : P.left.Opens)
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (F : P.left.Modules) [F.IsCoherent]
    (h_contains : Set.range (Scheme.zeroSchemeι L s) ⊆ (V : Set P.left))
    (hdepth : ∀ p : P.left, p ∉ Set.range (Scheme.zeroSchemeι L s) →
        ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P p)
        (RingedSpace.stalkModuleCat F p)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({p} : Set P.left))) > (1 : EInt))
    (e : openSystem P V L s F ≅ system P L s F 0) :
    IsIso (openComparison P V L s F ≫ (HasLimit.isoOfNatIso e).hom) := sorry

end AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology
