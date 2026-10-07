module

public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
import StacksCheckRecall

@[expose] public section

/- Remark 111.23.2 (1): finite generation of an A-module is Zariski-local on a
principal-open cover Spec(A) = ⋃ D(f_i), equivalently Ideal.span = ⊤. -/
@[stacks 02DX]
#check @Module.Finite.of_localizationSpan

/- Remark 111.23.2 (2): flatness of an A-module is Zariski-local on a
principal-open cover Spec(A) = ⋃ D(f_i), equivalently Ideal.span = ⊤. -/
@[stacks 02DX]
#check @Module.flat_of_localized_span

/- Remark 111.23.2 (3): finite presentation of an A-module is Zariski-local on a
principal-open cover Spec(A) = ⋃ D(f_i), equivalently Ideal.span = ⊤. -/
@[stacks 02DX]
#check @Module.FinitePresentation.of_localizationSpan
