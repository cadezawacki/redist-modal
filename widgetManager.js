

// pt/js/widgets/widgetManager.js
export class WidgetManager {
    constructor(context) {
        this.context = context;
        this.widgets = new Map();
        this.activeWidgetKey = null;
        this.isSwitching = false;
        this.mounted$ = this.context.page.createStore('mounted', false);
        this._setupReactions();
    }

    register(WidgetClass, widgetId, adapter, selector, config = {}) {
        if (!this.widgets.has(widgetId)) {
            // context, widgetId, feederId, manager, selector, config
            const instance = new WidgetClass(this.context, widgetId, adapter, selector, this, config);
            this.widgets.set(widgetId, { instance:instance });
        }
    }

    mount(grid) {
        this.grid = grid;
        this.mounted$.set('mounted', true);
    }

    _setupReactions() {
        this.mounted$.onChanges(async (c) => {
            return this.activeWidget()?.afterMount();
        }, {once: true});
    }

    initializeAllWidgets() {
        for (const widget of this.widgets.values()) {
            widget.instance._init().catch(e => {
                console.error(`Widget init failed for ${widget.instance.widgetId}:`, e);
            });
        }
    }

    async switch(targetKey) {
        if (this.isSwitching || (this.activeWidgetKey === targetKey)) return;

        const targetConfig = this.widgets.get(targetKey);
        if (!targetConfig) {
            console.error(`Widget with key '${targetKey}' is not registered.`);
            return;
        }

        this.isSwitching = true;
        try {
            const currentKey = this.activeWidgetKey;
            const currentConfig = currentKey ? this.widgets.get(currentKey) : null;

            if (currentConfig && typeof currentConfig.instance.deactivate === 'function') {
                currentConfig.instance.deactivate();
            }

            if (!targetConfig.instance.isInitialized) {
                await targetConfig.instance._init();
            }

            if (typeof targetConfig.instance.activate === 'function') {
                await targetConfig.instance.activate();
            }

            this.activeWidgetKey = targetKey;

            return {
                currentContainer: currentConfig ? currentConfig.instance.widgetDiv : null,
                targetContainer: targetConfig.instance.widgetDiv
            };
        } finally {
            this.isSwitching = false;
        }
    }

    activeWidget() {
        return this.widgets.get(this.activeWidgetKey)?.instance;
    }

    async cleanup() {
        for (const [key, config] of this.widgets.entries()) {
            if (config.instance.isInitialized) {
                if (config.instance && typeof config.instance.cleanup === 'function') {
                    try {
                        await config.instance.cleanup();
                    } catch (e) {
                        console.error(`Error cleaning up widget (${key})`, e)
                    }
                }
            }
        }
        this.widgets.clear();
    }

    setSwitching(state) {
        this.isSwitching = state;
    }
}
