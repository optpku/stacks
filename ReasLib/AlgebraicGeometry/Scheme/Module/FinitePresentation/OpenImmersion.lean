/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FinitePresentation

/-!
# Finitely presented modules and open immersions
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

/-- On a quasi-compact quasi-separated scheme, a morphism from a finitely presented module on
the domain of a quasi-compact open immersion to the restriction of a quasi-coherent module
extends to a morphism from a finitely presented module on the whole scheme. -/
theorem exists_finitePresentationMorphismExtension
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : U.Modules) [G.IsFinitePresentation]
    (φ : G ⟶ F.restrict j) :
    ∃ G' : X.Modules, G'.IsFinitePresentation ∧
      ∃ φ' : G' ⟶ F, ∃ e : G'.restrict j ≅ G,
        e.hom ≫ φ = (restrictFunctor j).map φ' := sorry

/-- Every finitely presented module on a quasi-compact open subscheme of a quasi-compact
quasi-separated scheme extends to a finitely presented module on the whole scheme. -/
theorem exists_finitePresentationExtension
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (G : U.Modules) [G.IsFinitePresentation] :
    ∃ G' : X.Modules, G'.IsFinitePresentation ∧ Nonempty (G'.restrict j ≅ G) := sorry

/-- On a quasi-compact quasi-separated scheme, a finite-type quasi-coherent module that is
finitely presented over a quasi-compact open subscheme admits a finitely presented epimorphic
approximation that is an isomorphism after restriction to that open subscheme. -/
theorem exists_finitePresentation_epi_restrictIso
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [(F.restrict j).IsFinitePresentation] :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (φ : G ⟶ F),
      Epi φ ∧ IsIso ((restrictFunctor j).map φ) := sorry

end AlgebraicGeometry.Scheme.Modules
