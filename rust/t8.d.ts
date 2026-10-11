interface Base { start(when?: number): void; }
interface Derived extends Base { start(when?: number, offset?: number, dur?: number): void; }
