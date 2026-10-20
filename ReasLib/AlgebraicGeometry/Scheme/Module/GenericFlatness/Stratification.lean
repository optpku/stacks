module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Stratum
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Generic flatness stratifications

This module records the existence of finite ideal-sheaf stratifications on which a finitely
presented module becomes flat over every successive locally closed stratum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented module along a finite-presentation morphism of quasi-compact,
quasi-separated schemes admits a finite descending chain of finite-type closed subschemes,
beginning with a thickening and ending in the empty subscheme, such that its pullback is flat over
every successive locally closed stratum. -/
theorem exists_genericFlatnessStratification
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S]
    [Scheme.Hom.FinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (t : ℕ) (Z : Fin (t + 1) → S.IdealSheafData)
      (h_finiteType : ∀ i : Fin (t + 1), (Z i).IsFiniteType)
      (h_thickening : IsThickening (Z 0).subschemeι)
      (h_chain : ∀ i : Fin t, Z i.castSucc ≤ Z i.succ)
      (h_last : Z (Fin.last t) = ⊤),
      ∀ i : Fin t,
        Scheme.Modules.flatOver
          ((Scheme.Modules.pullback (pullback.fst f (stratumMap Z i))).obj F)
          (pullback.snd f (stratumMap Z i)) := sorry

end AlgebraicGeometry.Scheme.Modules
