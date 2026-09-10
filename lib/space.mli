(** Phantom tags naming what a layout's input and output numbers mean.
    Polymorphic variants so the layout constructor can bound its domain:
    a layout's DOMAIN is a [source] space --- logical or thread-value ---
    never physical. Physical is terminal: nothing maps out of it. *)

type logical = [ `Logical ]
type physical = [ `Physical ]
type thread_value = [ `Thread_value ]

(** The spaces a layout may map FROM. *)
type source = [ logical | thread_value ]
