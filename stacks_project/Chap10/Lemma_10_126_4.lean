module

public import ReasLib.Algebra.Module.FinitePresentation.Localization
public import ReasLib.Algebra.Module.LocalizedModule.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Finite and Finitely Presented Localized Modules

The two clauses of Lemma 10.126.4 are already owned by the direct ReasLib
localization leaves imported above.

@stack 05N6
-/

/- Lemma 10.126.4 (1): if the localization `S⁻¹M` is finite over `S⁻¹R`,
there is a finite `R`-module `M'` and a map `M' → M` inducing a localized
linear equivalence. -/
@[stacks 05N6 "(1), finite localized module"]
#check @Module.Finite.exists_model_of_localized

-- A finite-submodule formulation is a lower-level construction available to proofs that need it.
@[stacks 05N6 "finite localized submodule support"]
#check @Submodule.exists_finite_of_localized_eq_top

/- Lemma 10.126.4 (2): if `S⁻¹M` is finitely presented over `S⁻¹R`, then it
is the localization of a finitely presented `R`-module mapping to `M`.  The
localized comparison map is the canonical `LocalizedModule.map`. -/
@[stacks 05N6 "(2), finitely presented localized module"]
#check @Module.FinitePresentation.exists_model_of_localized
