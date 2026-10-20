module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

#check (AlgebraicGeometry.SchemeOverField.PerfectDerived.IsPerfectFourierMukai :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
      [IsProper X.hom] [IsProper Y.hom],
      (PerfectDerived X ⥤ PerfectDerived Y) → Prop)

#check (AlgebraicGeometry.SchemeOverField.PerfectDerived.IsPerfectFourierMukai.exists_kernel :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
      [IsProper X.hom] [IsProper Y.hom]
      {F : PerfectDerived X ⥤ PerfectDerived Y} (hF : IsPerfectFourierMukai F),
      ∃ (K : @RingedSpace.ModuleDerived.Perfect
        (Limits.pullback X.hom Y.hom).toRingedSpace),
        Nonempty (F ≅ Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K))

#check (AlgebraicGeometry.SchemeOverField.PerfectDerived.IsPerfectFourierMukai.ofKernel :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
      [IsProper X.hom] [IsProper Y.hom]
      (K : @RingedSpace.ModuleDerived.Perfect
        (Limits.pullback X.hom Y.hom).toRingedSpace),
      IsPerfectFourierMukai (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K))

end
