module

public import ReasLib.Algebra.Module.Finite.BasicOpen
public import ReasLib.Algebra.Module.Flat.BasicOpen
import StacksCheckRecall

@[expose] public section

universe u v w

open PrimeSpectrum
open scoped PrimeSpectrum

/- Exercise 111.23.1 (1): if `Spec(A) = ⋃ D(f i)`, equivalently `(⨆ i, D(f i)) = ⊤`, and each
`LocalizedModule.Away (f i) M` is a finite module over `Localization.Away (f i)`, then `M` is a
finite `A`-module. -/
@[stacks 02DW]
#check (Module.Finite.of_basicOpen_cover :
  ∀ {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A) (hcover : (⨆ i, D(f i)) = ⊤)
    (h : ∀ i, Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) M)),
    Module.Finite A M)

/- Exercise 111.23.1 (2): if `Spec(A) = ⋃ D(f i)`, equivalently `(⨆ i, D(f i)) = ⊤`, and each
`LocalizedModule.Away (f i) M` is a flat module over `Localization.Away (f i)`, then `M` is a
flat `A`-module. -/
@[stacks 02DW]
#check (Module.Flat.of_basicOpen_cover :
  ∀ {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A) (hcover : (⨆ i, D(f i)) = ⊤)
    (h : ∀ i, Module.Flat (Localization.Away (f i)) (LocalizedModule.Away (f i) M)),
    Module.Flat A M)
