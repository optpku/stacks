module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.FieldPoints

/-!
# Galois-equivariant field spectra

Compatibility names for relative field spectra and their Galois actions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The spectrum of a field over the given base scheme. -/
abbrev specOver {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) : Over S :=
  FieldExtension.specOver σ

/-- The extension field spectrum over the given base scheme. -/
abbrev specExtend {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    Over S :=
  FieldExtension.specExtend σ k'

/-- The canonical projection of field spectra over the base scheme. -/
abbrev specExtendToOver {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    specExtend σ k' ⟶ specOver σ :=
  FieldExtension.specExtendToOver σ k'

/-- The scheme map induced by a Galois automorphism of the field extension. -/
abbrev galSpecMap {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (g : Gal(k'/k)) :
    Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k') :=
  FieldExtension.Galois.baseAut k k' g

/-- The left Galois action on the spectrum uses the inverse field automorphism. -/
abbrev galSpecAut {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    Gal(k'/k) →* Aut (Spec (CommRingCat.of k')) :=
  FieldExtension.Galois.specAut

end AlgebraicGeometry.Scheme.PreRelation
