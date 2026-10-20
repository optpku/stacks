module

public import ReasLib.Algebra.Module.Finite.BasicOpen
public import ReasLib.Algebra.Module.Flat.BasicOpen
public import ReasLib.Algebra.Module.FinitePresentation.BasicOpen
import StacksCheckRecall

@[expose] public section

universe u v w

open PrimeSpectrum
open scoped PrimeSpectrum

/- Remark 111.23.2 (1): finite generation of an A-module is Zariski-local on a
principal-open cover Spec(A) = ⋃ D(f_i), equivalently Ideal.span = ⊤. -/
@[stacks 02DX]
#check (Module.Finite.of_basicOpen_cover :
  ∀ {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A), (⨆ i, D(f i)) = ⊤ →
    (∀ i, Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) →
    Module.Finite A M)

/- Remark 111.23.2 (2): flatness of an A-module is Zariski-local on a
principal-open cover Spec(A) = ⋃ D(f_i), equivalently Ideal.span = ⊤. -/
@[stacks 02DX]
#check (Module.Flat.of_basicOpen_cover :
  ∀ {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A), (⨆ i, D(f i)) = ⊤ →
    (∀ i, Module.Flat (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) →
    Module.Flat A M)

/- Remark 111.23.2 (3): finite presentation of an A-module is Zariski-local on a
principal-open cover Spec(A) = ⋃ D(f_i), equivalently Ideal.span = ⊤. -/
@[stacks 02DX]
#check (Module.FinitePresentation.of_basicOpen_cover :
  ∀ {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A), (⨆ i, D(f i)) = ⊤ →
    (∀ i, Module.FinitePresentation (Localization.Away (f i))
      (LocalizedModule.Away (f i) M)) →
    Module.FinitePresentation A M)
