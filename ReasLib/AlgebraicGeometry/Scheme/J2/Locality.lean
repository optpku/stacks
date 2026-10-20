module

public import ReasLib.AlgebraicGeometry.Scheme.J2
public import ReasLib.RingTheory.Regular.JRing

/-!
# Locality of J-2 schemes

Open-cover and affine-coordinate-ring criteria for the J-2 property of locally Noetherian
schemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A locally Noetherian scheme is J-2 exactly when it admits an open cover by J-2 open
subschemes. -/
theorem isJ2_iff_exists_openCover [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, IsJ2 (𝒰.X i) := sorry

/-- A locally Noetherian scheme is J-2 exactly when every affine open has a J-2 section ring. -/
theorem isJ2_iff_forall_affineOpen_sectionsRing [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∀ U : X.affineOpens, IsJ2Ring.{u, u} (Γ(X, (U : X.Opens))) := sorry

/-- A locally Noetherian scheme is J-2 exactly when it admits an affine open cover whose
section rings are J-2. -/
theorem isJ2_iff_exists_affineOpenCover_sectionsRing [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsJ2Ring.{u, u} (Γ(X, (𝒰.f i).opensRange)) := sorry

/-- Being J-2, being J-2 on an open cover, having J-2 section rings on every affine open,
and having J-2 section rings on one affine open cover are equivalent for a locally Noetherian
scheme. -/
theorem isJ2_tfae [IsLocallyNoetherian X] :
    List.TFAE [
      IsJ2 X,
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, IsJ2 (𝒰.X i),
      ∀ U : X.affineOpens, IsJ2Ring.{u, u} (Γ(X, (U : X.Opens))),
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsJ2Ring.{u, u} (Γ(X, (𝒰.f i).opensRange))
    ] := sorry

end AlgebraicGeometry.Scheme
