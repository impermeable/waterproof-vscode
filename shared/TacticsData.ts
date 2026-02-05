export type Tactic = {
    label: string;
    type: string;
    detail: string;
    template: string;
    description: string;
    boost?: number;
    example?: string;
    advanced?: boolean;
};

export type TacticsData = Array<Tactic>;
