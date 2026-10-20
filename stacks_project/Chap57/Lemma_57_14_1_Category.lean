module

public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.KernelCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- The reusable smooth-proper Fourier--Mukai object carrier. -/
#check (FourierMukaiObject : Scheme.{u} → Type _)

/- The reusable perfect-kernel morphism carrier. -/
#check (fourierMukaiHom :
  ∀ {S : Scheme.{u}} (X Y : FourierMukaiObject S), Type _)

/- The canonical category structure on smooth proper Fourier--Mukai objects. -/
#check (fourierMukaiObjectCategory :
  ∀ (S : Scheme.{u}), Category (FourierMukaiObject S))

