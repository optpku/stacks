module

public import ReasLib.RingTheory.DedekindDifferent.Ideal
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec

@[expose] public section

noncomputable section

open scoped Algebra.TensorProduct.Right TensorProduct

universe u

/- The affine different ideal is provided by its reusable ring-theoretic owner. -/
#check (@Algebra.RelativeDualizingModule.differentIdeal :
  ∀ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B)
    (_ : IsNoetherianRing A) (_ : IsNoetherianRing B) (_ : Module.Finite A B)
    (_ : Module.Flat A B),
    Ideal B)

/- Its membership specification is provided by the reusable ring-theoretic owner. -/
#check (@Algebra.RelativeDualizingModule.mem_differentIdeal_iff :
  ∀ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B)
    (_ : IsNoetherianRing A) (_ : IsNoetherianRing B) (_ : Module.Finite A B)
    (_ : Module.Flat A B)
    (b : B),
    b ∈ Algebra.RelativeDualizingModule.differentIdeal A B ↔
      ∀ ω : Algebra.RelativeDualizingModule.of A B B (.of_moduleFinite) inferInstance,
        b • ω ∈
          Submodule.span B
            {Algebra.RelativeDualizingModule.finiteFlatTraceElement A B})

/- The ideal-valued Dedekind different is provided by the reusable owner. -/
#check (@Algebra.RelativeDualizingModule.dedekindDifferentIdeal :
  ∀ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B),
    Ideal B)

/- Its membership specification is provided by the reusable owner. -/
#check (@Algebra.RelativeDualizingModule.mem_dedekindDifferentIdeal_iff :
  ∀ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B)
    (_ : IsNoetherianRing A) (_ : IsNoetherianRing B) (_ : Module.Finite A B)
    (_ : Module.Flat A B)
    (b : B),
    b ∈ Algebra.RelativeDualizingModule.dedekindDifferentIdeal A B ↔
      algebraMap B (B ⊗[A] FractionRing A) b ∈
        Submodule.dedekindDifferent A (FractionRing A) B
          (B ⊗[A] FractionRing A))
