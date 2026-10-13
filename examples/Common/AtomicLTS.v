(** [AtomicLTS] moved to [models/simlin/AtomicLTS.v], so that the view
    theory in [models/view] does not depend on [examples].  This file
    re-exports it, and [Require Import examples.Common.AtomicLTS] keeps
    working unchanged. *)

Require Export models.simlin.AtomicLTS.
