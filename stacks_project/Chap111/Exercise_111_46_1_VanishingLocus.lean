module

public import ReasLib.AlgebraicGeometry.LinearSystem.VanishingLocus

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.LinearSystem.vanishingIdeal :
  ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L),
    (AlgebraicGeometry.LinearSystem.product X n).IdealSheafData)
