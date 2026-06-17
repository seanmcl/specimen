import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Tests for `derive_generator` command syntax variations and namespace handling. -/

set_option guard_msgs.diff true

namespace Foo

inductive Bar where
| bar

inductive Baz : Bar → Prop where
| isBar : Baz .bar

end Foo

--

#guard_msgs(drop info) in
derive_generator (∃ (b: Foo.Bar), Foo.Baz b)


section

open Foo

#guard_msgs(drop info) in
derive_generator (∃ (b: Bar), Baz b)


inductive Baz' : Bar → Bar → Prop where
| isBar2 : Baz' .bar .bar

-- `Bar` is single-constructor, so the derived match's `| _ => MFail` catch-all is
-- redundant; `match.ignoreUnusedAlts` (set by Specimen for derived code) drops it
-- silently. Previously this produced two `Redundant alternative` errors.
#guard_msgs(error, drop info) in
derive_generator (fun a => ∃ b, Baz' a b)

end
