/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Isomorphism
public import ReasLib.RingTheory.Extension.Generators.Reindex

/-!
# Reindexing naive cotangent complexes

This file packages the invariance of a presentationwise naive cotangent complex under an
equivalence of its generator type.  Both directions are induced by polynomial-variable
renaming; no isomorphism is selected from a Prop-valued existence statement.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace Algebra.Extension.NaiveCotangent

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι ι' : Type w}

/-- The inverse variable renaming composed with the forward renaming is the identity extension
morphism on the reindexed presentation. -/
theorem reindexFrom_comp_reindexTo (P : Algebra.Generators R S ι') (e : ι ≃ ι') :
    (Algebra.Generators.reindexFrom P e).toExtensionHom.comp
        (Algebra.Generators.reindexTo P e).toExtensionHom =
      .id (P.reindex e).toExtension := sorry

/-- The forward variable renaming composed with the inverse renaming is the identity extension
morphism on the original presentation. -/
theorem reindexTo_comp_reindexFrom (P : Algebra.Generators R S ι') (e : ι ≃ ι') :
    (Algebra.Generators.reindexTo P e).toExtensionHom.comp
        (Algebra.Generators.reindexFrom P e).toExtensionHom =
      .id P.toExtension := sorry

/-- Reindexing the variables of an algebra presentation induces a canonical isomorphism of its
naive cotangent complex. -/
@[stacks 07BN "reindexing invariance of the naive cotangent complex"]
noncomputable def reindexIso (P : Algebra.Generators R S ι') (e : ι ≃ ι') :
    complex (P.reindex e).toExtension ≅ complex P.toExtension :=
  isoOfHom (Algebra.Generators.reindexTo P e).toExtensionHom
    (Algebra.Generators.reindexFrom P e).toExtensionHom
    (reindexFrom_comp_reindexTo P e) (reindexTo_comp_reindexFrom P e)

/-- The forward morphism of `reindexIso` is the chain map induced by renaming variables along
the indexing equivalence. -/
theorem reindexIso_hom (P : Algebra.Generators R S ι') (e : ι ≃ ι') :
    (reindexIso P e).hom =
      chainMap (Algebra.Generators.reindexTo P e).toExtensionHom := sorry

/-- The inverse morphism of `reindexIso` is the chain map induced by renaming variables along
the inverse indexing equivalence. -/
theorem reindexIso_inv (P : Algebra.Generators R S ι') (e : ι ≃ ι') :
    (reindexIso P e).inv =
      chainMap (Algebra.Generators.reindexFrom P e).toExtensionHom := sorry

end Algebra.Extension.NaiveCotangent
