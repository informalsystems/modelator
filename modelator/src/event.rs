use std::any::Any;
use crate::tester::*;

pub enum Event<'a> {
    InitState(&'a dyn Any),
    NextState(&'a dyn Any),
    Action(&'a dyn Any),
}

pub trait StateSystem<State> {
    fn init(&mut self, state: State);
    fn next(&mut self, state: State);
}

pub trait ActionHandler<Action> {
    fn handle(&mut self, action: Action);
}


pub struct Runner<'a> {
    inits: Tester<'a>,
    nexts: Tester<'a>,
    actions: Tester<'a>,
}
