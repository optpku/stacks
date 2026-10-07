module

public import ReasLib.RingTheory.Smooth.Standard.BaseChange
public import ReasLib.RingTheory.Smooth.Standard.Element
public import ReasLib.RingTheory.Smooth.Standard.Equiv
public import ReasLib.RingTheory.Smooth.Standard.Localization
public import ReasLib.RingTheory.Smooth.Standard.Locus
public import ReasLib.RingTheory.Smooth.Standard.Normalized
public import ReasLib.RingTheory.Smooth.Standard.Presentation
public import ReasLib.RingTheory.Smooth.Standard.Retraction

/-!
# Standard elements of a presentation

This is the stable public façade for standard-element presentation APIs.
Fixed-presentation data lives in `Standard.Presentation`, while the global
element predicates live in `Standard.Element`. Matrix, localization, locus,
base-change, normalized-presentation, and retraction results live in focused
sibling leaves. Clients that need one layer only can import that leaf directly.
-/

@[expose] public section
