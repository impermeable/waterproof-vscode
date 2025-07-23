export class Debouncer {
    private _func: () => void;
    private _delay: number;

    private timer: number | undefined;

    constructor(delay: number, func: () => void) {
        this._func = func;
        this._delay = delay;
    }

    public call() {
        window.clearTimeout(this.timer);
        this.timer = window.setTimeout(() => {
            this._func();
        }, this._delay);
    }
}